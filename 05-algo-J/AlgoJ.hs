{-# LANGUAGE StrictData, OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-matches -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wno-unused-imports -Wno-name-shadowing #-}
{-# LANGUAGE PartialTypeSignatures #-}
import Data.STRef
import Control.Monad.ST
import Text.Show.Functions
import Control.Monad.Except
import Control.Monad.Trans.Class

data Lang =
  Var String
  | Lam String Lang
  | App Lang Lang
  | Let String Lang Lang
  | Number Int
  | Op (Int -> Int -> Int)
  | Boolean Bool
  | BOp (Int -> Int -> Bool)
  | ITE Lang Lang Lang
  deriving Show

data Ty a =
  TyPoly String
  | TyInt
  | TyBool
  | TyArr (Ty a) (Ty a)
  -- scope
  | TyRef (STRef a (Int, Maybe (Ty a)))



data Ty' =
  Ty'Poly String
  | Ty'Int
  | Ty'Bool
  | Ty'Arr Ty' Ty'
  | Ty'Ref Int (Maybe Ty')
  deriving Show

reify :: Ty s -> ST s Ty'
reify (TyPoly s) = pure $ Ty'Poly s
reify TyBool = pure Ty'Bool
reify TyInt = pure Ty'Int
reify (TyArr a b) = do
  a <- reify a
  b <- reify b
  pure $ Ty'Arr a b
reify (TyRef r) = do
  (i, v) <- readSTRef r
  case v of
    Just x -> do
        x <- reify x
        pure $ Ty'Ref i (Just x)
    Nothing -> pure $ Ty'Ref i Nothing

reify' :: ST s (Ty s) -> ST s Ty'
reify' t = do
  t <- t
  reify t

force :: Ty a -> ST a (Ty a)
force (TyRef r) = do
  (i, v) <- readSTRef r
  case v of
    Just x -> force x
    Nothing -> pure (TyRef r)
force (TyArr a b) = do
  a <- force a
  b <- force b
  pure $ TyArr a b
force x = pure x

newMeta :: Int -> ST a (Ty a)
newMeta lvl = do
  x <- newSTRef (lvl, Nothing)
  pure $ TyRef x

solveMeta :: STRef s (a1, Maybe a2) -> a1 -> a2 -> ST s ()
solveMeta m i k = do
  writeSTRef m (i, Just k)

fresh :: STRef s Int -> ST s String
fresh r = do
  x <- readSTRef r
  _ <- writeSTRef r (x + 1)
  pure $ "?m" ++ show x

meta' :: [(String, Ty a)]
     -> Int
     -> Ty a
     -> ST a ([(String, Ty a)], Ty a)
meta' map lvl TyBool = pure (map, TyBool)
meta' map lvl TyInt = pure (map, TyInt)
meta' map lvl (TyPoly s) =
  case lookup s map of
    Just v -> pure (map, v)
    Nothing -> do
      k <- newMeta lvl
      pure ((s, k) : map, k)
meta' map lvl (TyArr a b) = do
  (map', a') <- meta' map lvl a
  (map'', b') <- meta' map' lvl b
  pure (map'', TyArr a' b')
meta' map lvl (TyRef r) = do
         (i, v) <- readSTRef r
         case v of
           Just x -> do
             x <- force x
             (map', x') <- meta' map lvl x
             pure (map, x')
           Nothing -> pure (map, TyRef r)

meta :: Ty a -> Int -> ST a ([(String, Ty a)], Ty a)
meta x lvl = do
  x <- force x
  meta' [] lvl x

unmeta :: Int -> STRef a Int -> Ty a -> ST a (Ty a)
unmeta lvl gen (TyRef r) = do
  (i, v) <- readSTRef r
  if i < lvl then pure (TyRef r)
    else
    case v of
    Just x -> do
        inner <- unmeta lvl gen x
        writeSTRef r (i, Just inner)
        pure $ TyRef r
    Nothing -> do
        nm <- fresh gen
        _ <- solveMeta r i $ TyPoly nm
        pure $ TyRef r
unmeta lvl gen (TyArr a b) = do
  a <- unmeta lvl gen a
  b <- unmeta lvl gen b
  pure $ TyArr a b
unmeta _ gen x = pure x

mapJust :: (t -> a) -> Maybe t -> Maybe a
mapJust f Nothing = Nothing
mapJust f (Just x) = Just (f x)

unify' :: Ty a -> Ty a -> ExceptT String (ST a) ()
unify' (TyPoly a) (TyPoly b) | a == b = pure ()
unify' TyBool TyBool = pure ()
unify' TyInt TyInt = pure ()
unify' (TyArr a b) (TyArr q w) = do
  _ <- unify' a q
  _ <- unify' b w
  pure ()
unify' (TyRef a) (TyRef b) | a == b = pure ()
unify' (TyRef a) (TyRef b) = do
  (i, av) <- lift $ readSTRef a
  (j, bv) <- lift $ readSTRef b
  if i >= j then
    case bv of
      Just x -> undefined
      Nothing -> do
        lift $ solveMeta a j (TyRef b)
        pure ()
    else
    case av of
      Just x -> do
        undefined
      Nothing -> do
        lift $ solveMeta b i (TyRef a)
        pure ()

unify' (TyRef a) b = do
  (i, av) <- lift $ readSTRef a
  case av of
    Just x -> undefined -- impossible
    Nothing -> do
      lift $ solveMeta a i b
      pure ()
unify' b (TyRef a) = do
  (i, av) <- lift $ readSTRef a
  case av of
    Just x -> undefined -- impossible
    Nothing -> do
      _ <- lift $ solveMeta a i b
      pure ()
unify' a b = do
  a <- lift $ reify a
  b <- lift $ reify b
  throwError ("do not unify: " ++ show a ++ " & " ++ show b)

unify :: Ty a -> Ty a -> ExceptT String (ST a) ()
unify !a !b = do
  a <- lift $ force a
  b <- lift $ force b
  unify' a b

newtype Ctx a = Ctx (STRef a Int, Int, [(String, Ty a)])

maybeToEither :: a -> Maybe b -> Either a b
maybeToEither x Nothing = Left x
maybeToEither _ (Just x) = Right x

infer' :: Ctx a -> Lang -> ExceptT String (ST a) (Ty a)
infer' ctx (Boolean _) = pure TyBool
infer' ctx (Number _) = pure TyInt
infer' ctx (Op _) = pure $ TyArr (TyArr TyInt TyInt) TyInt
infer' ctx (BOp _) = pure $ TyArr (TyArr TyInt TyInt) TyBool
infer' ctx (Lam s x) = do
  let Ctx (gen, lvl, e) = ctx
  new <- lift $ newMeta lvl
  let ctx' = Ctx (gen, lvl + 1, (s, new) : e)
  body <- infer' ctx' x
  n <- lift $ force new
  pure $ TyArr n body
infer' ctx (Var s) = do
  let Ctx (_gen, lvl, env) = ctx
  case lookup s env of
    Just ty -> do
      (map, ty') <- lift $ meta ty lvl
      pure ty'
    Nothing -> throwError $ "binding not found: " ++ s
infer' ctx (ITE a b c) = do
  !bool <- infer' ctx a
  unify bool TyBool
  b' <- infer' ctx b
  c' <- infer' ctx c
  unify b' c'
  pure b'
infer' ctx (App f x) = do
  f' <- infer' ctx f
  f' <- lift $ force f'
  case f' of
    TyArr arg ret -> do
      x' <- infer' ctx x
      unify arg x'
      pure ret
    _ -> do
      r <- lift $ reify f'
      throwError ("application should have arrow type: " ++ show r)  -- bad
infer' ctx (Let x hd tl) = do
  hd' <- infer' ctx hd
  let Ctx (gen, lvl, env) = ctx
  hd' <- lift $ unmeta lvl gen hd'
  infer' (Ctx (gen, lvl, (x, hd') : env)) tl

infer :: Lang -> ExceptT String (ST s) (Ty s)
infer tm = do
  gen <- lift $ newSTRef 0
  let ctx = Ctx(gen, 0, [])
  ty <- infer' ctx tm
  ty <- lift $ unmeta (-1) gen ty
  lift $ force ty

-- modify this bit

app3 :: Lang -> Lang -> Lang -> Lang
app3 a b = App (App a b)

term :: Lang
term = Lam "b" (Lam "x" (Let "f" (Lam "y" (ITE (Var "b") (Var "x") (Var "y"))) (Var "f")))

term' :: ST s (Either String Ty')
term' = do
  ty <- runExceptT $ infer term
  case ty of
    Right t -> do
      r <- reify t
      pure $ Right r
    Left s -> pure $ Left s

main :: IO ()
main = do
  let ty = runST term'
  putStrLn ""
  putStrLn $ "term: " ++ show term
  putStrLn $ "type: " ++ show ty