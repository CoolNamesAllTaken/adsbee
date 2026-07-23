#!/bin/bash
# Enforce the firmware/AGENTS.md rule: a change to the Settings struct (kSettingsVersion) must be
# accompanied by a firmware version bump. Otherwise the RP2040 won't detect a version mismatch and
# won't reflash the ESP32/CC1312, leaving them on a stale build with a mismatched Settings struct
# (SPI sync failures, reboots).
#
# Compares the two coupled version numbers between an "old" and a "new" source and fails if the
# settings version changed without a matching firmware version bump.
#
# Usage: check_version_sync.sh <old_source> <new_source>
#   Each source is one of:
#     WORKTREE   - the current files on disk (unstaged + staged changes)
#     INDEX      - the staged (about-to-be-committed) content
#     <git-ref>  - any git revision, e.g. HEAD, origin/main, a commit SHA
#
#   Examples:
#     check_version_sync.sh HEAD WORKTREE      # local build: committed vs working tree
#     check_version_sync.sh HEAD INDEX         # pre-commit hook: committed vs staged
#     check_version_sync.sh origin/main HEAD   # CI: base branch vs PR head

set -euo pipefail

old_source="${1:-HEAD}"
new_source="${2:-WORKTREE}"

# Paths (relative to repo root) that hold the two coupled version numbers.
settings_file="firmware/common/settings/settings.hh"
firmware_version_file="firmware/common/coprocessor/object_dictionary.cpp"

root=$(git rev-parse --show-toplevel 2>/dev/null) || {
    echo "WARNING: not inside a git repository, skipping version sync check."
    exit 0
}

# Read a file's contents from a given source. Fails loudly if the source can't be
# read (bad ref, missing file) rather than silently treating it as empty.
read_source() {
    local source="$1" file="$2"
    case "$source" in
        WORKTREE) cat "$root/$file" ;;
        INDEX)    git -C "$root" show ":$file" ;;
        *)        git -C "$root" show "$source:$file" ;;
    esac
}

# Extract the integer value(s) of a constant from a file at a given source.
# Uses POSIX extended regex (grep -E) so it works on GNU and BSD/macOS grep alike
# (grep -P / \K is not portable and silently no-ops on BSD grep).
# Usage: extract <source> <repo-relative-file> <constant-name-ERE>
extract() {
    local source="$1" file="$2" name="$3"
    read_source "$source" "$file" \
        | grep -oE "${name}[[:space:]]*=[[:space:]]*[0-9]+" \
        | grep -oE '[0-9]+$'
}

echo "=== Checking Settings/firmware version sync ($old_source -> $new_source) ==="

# Extract at the top level (NOT inside an `if`/`&&`), so `set -e` + `pipefail`
# abort loudly on a read failure (bad ref, missing file, or a constant that
# grep can't find) instead of masking it as "unchanged" and passing silently.
settings_old=$(extract "$old_source" "$settings_file" kSettingsVersion)
settings_new=$(extract "$new_source" "$settings_file" kSettingsVersion)
firmware_old=$(extract "$old_source" "$firmware_version_file" 'kFirmwareVersion[A-Za-z]+')
firmware_new=$(extract "$new_source" "$firmware_version_file" 'kFirmwareVersion[A-Za-z]+')

if [ "$settings_old" != "$settings_new" ] && [ "$firmware_old" = "$firmware_new" ]; then
    echo "ERROR: kSettingsVersion changed but the firmware version in"
    echo "       $firmware_version_file was not bumped."
    echo "Fix: bump kFirmwareVersionPatch (or kFirmwareVersionReleaseCandidate for dev builds),"
    echo "     then commit it together with the settings change."
    exit 1
fi

# Broader guard (warning). The RP2040 flashes itself from the .uf2 but only reflashes the ESP32 and
# CC1312 coprocessors when their reported firmware version differs from its own (main.cc). So any
# change to coprocessor firmware -- the ESP32 app, the CC1312 app, or the shared common/ code both
# compile -- that is NOT paired with a firmware version bump silently leaves the coprocessors
# running a stale build. Warn rather than fail: harmless edits (comments, formatting) also trip it,
# and a bump is cheap.
coprocessor_paths=(
    "firmware/adsbee_1090/esp"
    "firmware/adsbee_1090/ti"
    "firmware/common"
)

# True (exit 0) if any of the given paths differ between old_source and new_source.
paths_changed() {
    local old="$1" new="$2"
    shift 2
    case "$new" in
        WORKTREE) ! git -C "$root" diff --quiet "$old" -- "$@" ;;
        INDEX)    ! git -C "$root" diff --quiet --cached "$old" -- "$@" ;;
        *)        ! git -C "$root" diff --quiet "$old" "$new" -- "$@" ;;
    esac
}

if [ "$firmware_old" = "$firmware_new" ] && paths_changed "$old_source" "$new_source" "${coprocessor_paths[@]}"; then
    echo "WARNING: coprocessor firmware (ESP32 / CC1312 / shared common/) changed but the version in"
    echo "         $firmware_version_file was NOT bumped."
    echo "         The RP2040 only reflashes the coprocessors on a version mismatch, so they will keep"
    echo "         running STALE firmware after 'just flash'. Bump kFirmwareVersionPatch (or"
    echo "         kFirmwareVersionReleaseCandidate for dev builds) to force the reflash."
    exit 1
fi

echo "=== Version sync check passed ==="
