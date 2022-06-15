def main():
    import sys
    with open(sys.argv[1]) as f:
        s = f.read()
    output = []
    for line in s.split():
        i = int(line, 2)
        assert 0 <= i < 2**16
        # little endian
        output.append(chr(i & 0xff))
        output.append(chr((i >> 8) & 0xff))
    print(output)
    with open(sys.argv[1] + ".bin", "wb") as f:
        f.write(b"".join(output))


if __name__ == '__main__':
    main()
