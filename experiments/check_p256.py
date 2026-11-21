#!/usr/bin/env python3
"""Cross-check p256.py against OpenSSL.

OpenSSL generates P-256 key pairs; for each one this script recomputes the
public point from the private scalar with p256.mul and compares the two. It
also checks a few group identities. Requires the ``openssl`` command line
tool; p256.py itself needs only the standard library.

Usage:
  python3 check_p256.py [--keys N]
"""

import argparse
import os
import re
import subprocess
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import p256


def openssl_keypair():
    pem = subprocess.run(
        ["openssl", "ecparam", "-name", "prime256v1", "-genkey", "-noout"],
        check=True, capture_output=True).stdout
    text = subprocess.run(
        ["openssl", "ec", "-text", "-noout", "-conv_form", "uncompressed"],
        input=pem, check=True, capture_output=True).stdout.decode()
    text = text.replace("\r\n", "\n")
    blocks = {}
    for name in ("priv", "pub"):
        m = re.search(name + r":\s*\n((?:\s+[0-9a-f:]+\n)+)", text)
        blocks[name] = bytes.fromhex(re.sub(r"[\s:]", "", m.group(1)))
    d = int.from_bytes(blocks["priv"], "big")
    pub = blocks["pub"]
    assert pub[0] == 4 and len(pub) == 65
    return d, (int.from_bytes(pub[1:33], "big"), int.from_bytes(pub[33:], "big"))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--keys", type=int, default=100)
    args = ap.parse_args()
    version = subprocess.run(["openssl", "version"], capture_output=True,
                             text=True).stdout.strip()
    matches = 0
    for _ in range(args.keys):
        d, pub = openssl_keypair()
        if p256.mul(d, p256.G) == pub and p256.is_on_curve(pub):
            matches += 1
    G = p256.G
    identities = {
        "(N-1)G = -G": p256.mul(p256.N - 1, G) == (p256.GX, (-p256.GY) % p256.P),
        "2G = G + G": p256.mul(2, G) == p256.add(G, G),
        "(a+b)G = aG + bG": p256.mul(12345 + 67890, G)
        == p256.add(p256.mul(12345, G), p256.mul(67890, G)),
    }
    print(version)
    print("public keys reproduced: {}/{}".format(matches, args.keys))
    for name, ok in identities.items():
        print("{}: {}".format(name, "ok" if ok else "FAIL"))
    passed = matches == args.keys and all(identities.values())
    print("RESULT: {}".format("PASS" if passed else "FAIL"))
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
