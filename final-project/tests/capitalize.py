s = "CoMPliCaTED caPitALIzatiON"
length = len(s)
a = ord("a")
z = ord("z")
diff = ord("A") - ord("a")
i = 0
while i < length:
    ch = ord(s[i])
    if ch >= a and ch <= z:
        s[i] = chr(ch + diff)
    i = i + 1
print(s)