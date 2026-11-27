LeanCalc
========

A standalone Apple-silicon macOS spreadsheet, with application and calculation
logic written in Lean, compiled to C, and linked to Tcl/Tk. Current application:
0.5.1, build 11. macOS 14 or later. The orange column-chart logo is the selected
project icon.

Features
--------
- Up to 32 named sheets, each with 100-1,000 rows and columns A-Z.
- Sparse working storage, dependency tracking and cached display results.
- Exact rational arithmetic and 81 supported function names, including math,
  conditional aggregates, exact-match lookups, text and date functions.
- Formula range picking, mixed/absolute/cross-sheet references, rectangular
  copy/cut/paste/fill, structural edits, and workbook-wide undo/redo.
- CSV import/export, native .lcalc persistence (versions 1-4), and a declared,
  limited ODS/OpenFormula subset with explicit unsupported-feature diagnostics.
- Formatting, find/sort/filter, printable HTML, named ranges, validation,
  conditional formatting, charts, embedded PNGs, pivot tables and declarative
  custom-function packs.
- Finder/Dock file-open handling for .lcalc, .csv and supported .ods files.
  Imported CSV/ODS remains an unsaved native workbook; the source is unchanged.

Build from this checkout
------------------------
Prerequisites: Apple Command Line Tools, Lean 4.35.0-rc3, Python 3.9 or later,
Homebrew GMP and libuv (static libraries), and LaTeX/latexmk. Tcl/Tk 9.0.4 runtime
libraries and resources are included under vendor/tcltk-9.0.4. The build expects
Apple-silicon Homebrew libraries under /opt/homebrew/lib.

Install GMP, libuv and LaTeX (BasicTeX plus the packages the manual uses), then
open a new terminal so latexmk is on the PATH:

  brew install gmp libuv
  brew install --cask basictex
  sudo tlmgr update --self
  sudo tlmgr install latexmk lastpage enumitem fancyhdr booktabs microtype \
    psnfss mathpazo fpl palatino

Homebrew's static GMP and libuv only run on the macOS version they were built for
(currently 15 and 26). To keep macOS 14 support, build both for macOS 14 once
(needs cmake; the build then uses them automatically):

  python3 lean_calc/build_compat_libs.py

Without them, the build warns and marks the app with the newer minimum macOS.

Then build:

  python3 lean_calc/build.py

LaTeX is only needed for the PDF manual. Without it, run every test and keep the
existing LeanCalc.pdf:

  python3 lean_calc/build.py --skip-manual

The default Lean toolchain location is:
  ~/.elan/toolchains/leanprover--lean4---v4.35.0-rc3

Override dependencies when needed:
  python3 lean_calc/build.py --toolchain /path/to/toolchain --tk-bundle /path/to/runtime

Build outputs:
  dist/LeanCalc.app
  dist/LeanCalc-AppleSilicon.zip
  dist/Diagnose LeanCalc.command

Save work and quit a running copy before rebuilding its app bundle. The supplied
app needs none of the development tools to run. The builder runs automated tests,
compiles the manual, signs the app locally, verifies it, and packages the ZIP.
Generated apps and build files are intentionally excluded from Git.

Tests and documentation
-----------------------
The current release passes 496 named native/headless checks, including 17
file-opening checks. For a standalone recheck and PDF build:

  python3 lean_calc/build_document.py

Desktop checks (require an interactive macOS session):
  dist/LeanCalc.app/Contents/MacOS/LeanCalc --gui-self-test
  dist/LeanCalc.app/Contents/MacOS/LeanCalc --gui-render-benchmark

Read LeanCalc.pdf for the complete feature scope, formula semantics, test
catalogue, and five-phase roadmap. lean_calc/phase-completion.txt records the
remaining acceptance gates. Real desktop appearance/gestures and live Apache
OpenOffice comparison have not been verified in the restricted development
session. Headless tests do not establish those acceptance gates.

Formal verification has not begun; its manual section is deliberately blank.
XLSX and executable macros are not supported.

Useful examples are in lean_calc/examples/, including Features-gallery.lcalc,
Pivot-gallery.lcalc, Phase2-workbook.lcalc and Interoperability.ods.

Repository layout
-----------------
lean_calc/              Lean/C sources, tests, builders, fixtures and examples
lean_calc/assets/       Selected application artwork
lean_calc/vendor/       C headers, ODF schema and third-party notices
vendor/tcltk-9.0.4/     Runtime dependencies for reproducible app packaging
LeanCalc.tex/pdf         Manual source and compiled guide
AGENTS.md               Workspace communication preferences
build_answers.py        Optional local conversation-log PDF builder

Private notes, credentials, conversation logs, drafts and temporary files are
excluded by .gitignore. A local answers.tex, when present, is compiled alongside
the manual; it is not required to build a clean checkout.
