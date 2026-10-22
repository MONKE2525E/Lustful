#!/usr/bin/env bash
# Path-source differential only; not registry admission or a full graph audit.
# LUST=/absolute/path/to/lust bash scripts/test-json-source-adapter.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
cases=$root/tests/json-source-adapter
: "${LUST:?set LUST to the compiler executable}"
lust_bin=$(realpath "$(command -v "$LUST")")
work=$(mktemp -d "${TMPDIR:-/tmp}/lust-json-source.XXXXXX")
echo "JSON source differential artifacts: $work"
mkdir -p "$work/oracle/src/bin" "$work/source/src/bin" "$work/deny-host"
cat >"$work/oracle/Cargo.toml" <<'MANIFEST'
[package]
name = "json-oracle"
version = "0.0.0"
edition = "2024"
[workspace]
[dependencies]
MANIFEST
cat "$cases/oracle-deps.toml" >>"$work/oracle/Cargo.toml"
# This path dependency is not a substituted registry package.
cat >"$work/source/Cargo.toml" <<MANIFEST
[package]
name = "json-source"
version = "0.0.0"
edition = "2024"
[workspace]
[dependencies]
serde_json = { path = "$root/library/deps/serde_json" }
MANIFEST
for f in "$cases"/pass/*.rs "$cases"/reject/*.rs; do
    name=$(basename "$f" .rs)
    cp "$f" "$work/oracle/src/bin/$name.rs"
    cp "$f" "$work/source/src/bin/$name.rs"
done
# The upstream must compile every valid-upstream rejection case as well.
CARGO_NET_OFFLINE=true timeout 600 cargo build --quiet \
    --manifest-path "$work/oracle/Cargo.toml" --bins \
    --target-dir "$work/oracle-target" >"$work/oracle-build.out" 2>"$work/oracle-build.err"
for f in "$cases"/pass/*.rs; do
    name=$(basename "$f" .rs)
    timeout 30 "$work/oracle-target/debug/$name" >"$work/$name.oracle.out"
done
for f in "$cases"/malformed/*.rs; do
    name=malformed_$(basename "$f" .rs)
    cp "$f" "$work/oracle/src/bin/$name.rs"
    set +e
    CARGO_NET_OFFLINE=true timeout 120 cargo build --quiet \
        --manifest-path "$work/oracle/Cargo.toml" --bin "$name" \
        --target-dir "$work/oracle-target" >"$work/$name.oracle.out" 2>"$work/$name.oracle.err"
    status=$?
    set -e
    if [ "$status" -eq 0 ] || [ "$status" -ge 124 ] ||
        ! rg -q '^error' "$work/$name.oracle.err" ||
        ! rg -q 'could not compile .*json-oracle' "$work/$name.oracle.err"; then
        echo "oracle malformed case did not reject normally: $name ($status)" >&2
        exit 1
    fi
done
# Smoke guard only: parent must separately audit transitive execs and clean discovery.
cat >"$work/deny-host/rustc" <<'GUARD'
#!/bin/sh
echo "forbidden host compiler invocation" >>"$JSON_HOST_LOG"
exit 97
GUARD
chmod +x "$work/deny-host/rustc"
export JSON_HOST_LOG=$work/forbidden-host.log
export RUSTC=$work/deny-host/rustc
export RUSTC_WRAPPER=
export RUSTC_WORKSPACE_WRAPPER=
export PATH=$work/deny-host:$PATH
export CARGO_TARGET_DIR=$work/source-target
export CARGO_NET_OFFLINE=true
export LUST_CACHE_DIR=$work/source-cache
export LUST_HOST_TOOLS=0
export LUST_NO_DAEMON=1
export LUST_NO_CACHE=1
unset RUSTFLAGS CARGO_ENCODED_RUSTFLAGS || true
lust_build() {
    local label=$1
    shift
    if [ "${JSON_TRACE:-0}" = 1 ]; then
        strace --kill-on-exit -f -qq -s 4096 -e trace=execve,execveat \
            -o "$work/$label.trace" timeout 120 "$lust_bin" "$@"
    else
        timeout 120 "$lust_bin" "$@"
    fi
}
for f in "$cases"/pass/*.rs; do
    name=$(basename "$f" .rs)
    emit=()
    [ "${SANITIZE:-0}" != 1 ] || emit=(--emit-c "$work/$name.generated")
    lust_build "$name" build "$work/source/src/bin/$name.rs" \
        --manifest-path "$work/source/Cargo.toml" --bin "$name" -o "$work/$name.lust" \
        "${emit[@]}" \
        >"$work/$name.build.out" 2>"$work/$name.build.err"
    timeout 30 "$work/$name.lust" >"$work/$name.lust.out"
    cmp "$work/$name.oracle.out" "$work/$name.lust.out"
    if [ "${SANITIZE:-0}" = 1 ]; then
        timeout 120 gcc -O1 -w -Werror=incompatible-pointer-types \
            -fno-sanitize-recover=undefined -fsanitize=address,undefined \
            -o "$work/$name.sanitized" "$work/$name.generated".*.c -lm \
            >"$work/$name.sanitize-build.out" 2>"$work/$name.sanitize-build.err"
        ASAN_OPTIONS=detect_leaks=1:allocator_may_return_null=1 \
            timeout 30 "$work/$name.sanitized" >"$work/$name.sanitized.out" 2>"$work/$name.sanitized.err"
        if rg -q 'runtime error|Sanitizer' "$work/$name.sanitized.err"; then
            cat "$work/$name.sanitized.err" >&2
            exit 1
        fi
        cmp "$work/$name.oracle.out" "$work/$name.sanitized.out"
    fi
    echo "source match: $name"
done
# Record actual diagnostics; crashes/timeouts/admission failures do not count.
for kind in reject adapter-reject malformed; do
    for f in "$cases/$kind"/*.rs; do
        name=${kind//-/_}_$(basename "$f" .rs)
        cp "$f" "$work/source/src/bin/$name.rs"
        set +e
        lust_build "$name" build "$work/source/src/bin/$name.rs" \
            --manifest-path "$work/source/Cargo.toml" --bin "$name" -o "$work/$name.lust" \
            >"$work/$name.build.out" 2>"$work/$name.build.err"
        status=$?
        set -e
        if [ "$status" -eq 0 ] || [ "$status" -ge 124 ] ||
            ! rg -q 'L[0-9]{4}' "$work/$name.build.err"; then
            echo "case did not produce a normal Lust rejection: $name ($status)" >&2
            exit 1
        fi
        if rg -q 'L0508|L0532|forbidden host compiler' "$work/$name.build.err"; then
            echo "case rejected at admission/host preparation: $name" >&2
            exit 1
        fi
        if [ "$kind" = reject ] && ! rg -q 'L0612' "$work/$name.build.err"; then
            echo "conversion rejected without expected bound diagnostic: $name" >&2
            exit 1
        fi
        echo "source reject: $name (inspect $work/$name.build.err)"
    done
done
if [ -e "$JSON_HOST_LOG" ]; then
    echo "source phase attempted forbidden host compiler work" >&2
    exit 1
fi
echo "Source comparison completed; registry and full graph checks remain separate."
