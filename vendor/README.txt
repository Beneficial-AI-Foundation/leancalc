Tcl/Tk 9.0.4 runtime
===================

The Apple-silicon Tcl/Tk runtime in tcltk-9.0.4 is copied byte-for-byte from the
existing EditorLean project's vendor/tcltk-9.0.4 dependency. It contains the two
runtime libraries, Tcl and Tk script/resource trees, and Tcl package resources.
It is a build dependency, independent of any generated application bundle.

The corresponding licenses are included in:
  ../lean_calc/vendor/Tcl-license.terms
  ../lean_calc/vendor/Tk-license.terms

The LeanCalc builder copies these libraries and resources into the app bundle
and includes the licenses there. It signs the copied libraries locally.
