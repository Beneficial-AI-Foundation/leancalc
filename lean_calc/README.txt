LeanCalc 0.5.1
==============

The current project overview and build instructions are in ../README.txt.
The complete manual is ../LeanCalc.pdf (source: ../LeanCalc.tex).

Build from the project root:
  python3 lean_calc/build.py

This uses the included ../vendor/tcltk-9.0.4 runtime, runs 490 native/headless
checks, compiles documentation, signs dist/LeanCalc.app and packages its ZIP.
Lean 4.35.0-rc3, Apple Command Line Tools, Python 3, Homebrew GMP/libuv static
libraries and LaTeX/latexmk are required. The application itself is standalone.

Source modules, tests and fixtures are in this directory. generated/ and .olean
files are rebuildable outputs excluded from Git. Native format version 4 retains
workbook objects; versions 1-3 are read for migration. CSV and the declared ODS
subset are supported; XLSX and executable macros are not implemented.

See phase-completion.txt for desktop and OpenOffice acceptance still pending.
