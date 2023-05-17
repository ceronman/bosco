import argparse
from pathlib import Path
from subprocess import run

SNIPPET = Path("snippet.bosco")

parser = argparse.ArgumentParser()
parser.add_argument('name', type=str, help='name of the test')
parser.add_argument('-l', '--lexer', action=argparse.BooleanOptionalAction)
args = parser.parse_args()

if args.lexer:
    testdir = Path("lexer_tests")
    option = "-tokens"
else:
    testdir = Path("tests")
    option = "-tree"

code = SNIPPET.open("rb").read().strip()

result = run(f"antlr4-parse Bosco.g4 program {option}", input=code, shell=True, capture_output=True)

name = args.name if args.name.endswith(".test") else f"{args.name}.test"

with testdir.joinpath(name).open("wb") as testfile:
    testfile.write(code)
    testfile.write(b"\n//" + b'-' * 80 + b'\n')
    testfile.write(result.stdout.strip())