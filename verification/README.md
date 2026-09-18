# Verification record

Machine-produced evidence for the claims in the [top-level README](../README.md). Every file
here is raw output of the command named beside it, captured on 2026-09-18 from a clean rebuild.

| File | Command | Result |
|---|---|---|
| [`build.log`](build.log) | `rm -rf .lake/build && lake build` | exit 0, 3149 jobs, 32.6s |
| [`axioms.log`](axioms.log) | `lake env lean Erdos815/Verify.lean` | 51 declarations audited |
| [`scan.log`](scan.log) | placeholder and escape-hatch scan over every tracked `.lean` file | see the file |
| [`CHECKSUMS.txt`](CHECKSUMS.txt) | `git ls-files \| xargs shasum -a 256` | sha256 of every tracked file |

## Reproduce it yourself

```bash
lake exe cache get            # prebuilt Mathlib oleans, several GB
rm -rf .lake/build
lake build
lake env lean Erdos815/Verify.lean > mine.log
diff <(grep 'depends on axioms' mine.log | sort) \
     <(grep 'depends on axioms' verification/axioms.log | sort)
shasum -a 256 -c <(grep -v '^#' verification/CHECKSUMS.txt)
```

The pins that make this reproducible are [`lean-toolchain`](../lean-toolchain) and
[`lake-manifest.json`](../lake-manifest.json). Moving either one invalidates this record.

## What the record settles, and what it leaves open

It settles three things: the sources compile, they carry no placeholder and no escape hatch, and
the kernel accepts every audited declaration using only `propext`, `Classical.choice` and
`Quot.sound`. Lines reporting a subset of those three are stronger rather than weaker.

It leaves open whether the Lean statement says what the original problem says. That question is
human review, and the document for it is [`docs/FAITHFULNESS.zh.md`](../docs/FAITHFULNESS.zh.md), the line-by-line comparison with the paper.
