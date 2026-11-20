#!/bin/zsh
# Start this specific build without going through application activation.
# The log contains startup diagnostics, not document text.
set -u
calc_diag_dir="${0:A:h}"
calc_diag_app="$calc_diag_dir/LeanCalc.app/Contents/MacOS/LeanCalc"
calc_diag_log="$calc_diag_dir/LeanCalc-startup.log"
if [[ ! -x "$calc_diag_app" ]]; then
    print -r -- "LeanCalc.app must be beside this launcher."
    read -r '?Press Return to close.'
    exit 1
fi
{
    print -r -- "LeanCalc desktop startup diagnostic"
    /bin/date -u
    print -r -- "Executable: $calc_diag_app"
    "$calc_diag_app" --version
    /usr/bin/sw_vers
} > "$calc_diag_log" 2>&1
print -r -- "Starting LeanCalc directly."
print -r -- "Log: $calc_diag_log"
print -r -- "If the editor opens, you can use it normally."
print -r -- "If it hangs or fails, tell me; the log is saved automatically."
LEANCALC_DIAGNOSTICS=1 "$calc_diag_app" >> "$calc_diag_log" 2>&1
calc_diag_exit=$?
print -r -- "Process exit status: $calc_diag_exit" >> "$calc_diag_log"
/bin/cat "$calc_diag_log"
read -r '?Press Return to close this Terminal window.'
exit "$calc_diag_exit"
