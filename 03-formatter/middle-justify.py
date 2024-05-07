s = ""
while True:
    x = input()
    if not x:
        break
    s += (x.strip() + '\n')


arr = []
for line in s.split("\n"):
    arr += [(len(line))]

m = max(arr) // 2

for line in s.split("\n"):
    pad = m - (len(line) // 2)
    pad = pad * " "
    print(pad + line)
