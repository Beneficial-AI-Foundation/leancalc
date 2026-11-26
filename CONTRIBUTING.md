# Contributing to LeanCalc

Thanks for your interest in contributing. LeanCalc is a standalone Apple-silicon
macOS spreadsheet whose application and calculation logic is written in Lean,
compiled to C, and linked to Tcl/Tk 9. This guide covers how to build it, how it is
checked, and how to send a change. It follows the shared contribution standard used
across the [Beneficial AI Foundation](https://github.com/Beneficial-AI-Foundation)
Lean projects.

LeanCalc targets **Apple-silicon macOS 14 or later only**. There is no Lake project,
and no Windows or Linux build — the build is driven by `lean_calc/build.py`.

## Prerequisites

- Apple Command Line Tools (`xcode-select --install`).
- [`elan`](https://github.com/leanprover/elan) with Lean **4.35.0-rc3** (pinned in
  `lean_calc/lean-toolchain`); `build.py` looks for it under
  `~/.elan/toolchains/leanprover--lean4---v4.35.0-rc3`, or pass `--toolchain`.
- Python 3.9 or later.
- Homebrew `gmp` and `libuv` (the **static** libraries, under `/opt/homebrew/lib`).
- LaTeX / `latexmk` (only for the manual and the full packaged build).
- The Tcl/Tk 9.0.4 runtime is vendored under `vendor/tcltk-9.0.4`; no install needed.

## Building

The full build — Lean → C → native binary, the signed `LeanCalc.app`, the manual and
the `.zip` — is one command from the project root:

```sh
python3 lean_calc/build.py
```

Outputs land in `dist/` (`LeanCalc.app`, `LeanCalc-AppleSilicon.zip`,
`Diagnose LeanCalc.command`). Save work and quit any running copy before rebuilding
its app bundle.

Continuous integration (`.github/workflows/ci.yml`) does the light part on `macos-14`:
it compiles the Lean sources to the native `LeanCalc` binary and runs the headless
self-tests. It does **not** build the LaTeX manual, code-sign, or bundle the Tcl/Tk
data trees, so it does not need LaTeX. The release workflow packages that native
binary with the vendored Tcl/Tk runtime dylibs; the full signed `.app` is produced by
`build.py` locally.

## Testing

```sh
python3 lean_calc/build.py          # builds and runs the full native/headless checks
python3 lean_calc/build_document.py # standalone recheck + rebuilds LeanCalc.pdf
```

The current release passes 490 named native/headless checks. You can run individual
suites directly against the built binary (headless, no desktop session needed), e.g.:

```sh
dist/LeanCalc.app/Contents/MacOS/LeanCalc --self-test
dist/LeanCalc.app/Contents/MacOS/LeanCalc --phase2-self-test
```

Desktop checks need an interactive macOS session:

```sh
dist/LeanCalc.app/Contents/MacOS/LeanCalc --gui-self-test
```

Please make sure the build and the self-tests pass before opening a PR. See
`lean_calc/phase-completion.txt` for the acceptance gates still pending; formal
verification has not begun, and its manual section is deliberately blank.

## Submitting a change

1. **Branch** off `main` (or fork the repository).
2. Keep each pull request focused, and add or update a test/fixture for behaviour you
   change (the suites and fixtures live under `lean_calc/`).
3. Make sure `python3 lean_calc/build.py` succeeds and the self-tests pass. Generated
   apps, `.olean` files and build outputs are intentionally excluded from Git — do not
   commit them.
4. Write a clear PR description: what changed, why, and how you verified it.
5. By contributing, you agree your contribution is licensed under this repository's
   license (MIT, see `LICENSE`), and you certify the
   [Developer Certificate of Origin](https://developercertificate.org/) — add a
   `Signed-off-by: Your Name <you@example.com>` line to your commits (`git commit -s`).

## Reporting issues

Open a GitHub issue with a clear title, what you expected, what happened, and the
smallest workbook or steps that reproduce it. Security-sensitive reports can be sent
privately to **support@beneficialaifoundation.org** instead of a public issue.

## Code of conduct

Be respectful and constructive. Harassment or abuse is not tolerated. Maintainers may
remove comments, commits or contributions that don't meet this standard.
