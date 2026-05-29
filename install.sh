#!/usr/bin/env bash
#
# qed installer.  Usage:
#   curl -sSfL https://raw.githubusercontent.com/JacobAsmuth/qed/main/install.sh | sh
#
# Installs the Lean toolchain (elan) if missing, fetches the qed framework into
# ~/.qed/qed, builds the qed CLI, and puts a `qed` launcher on PATH. The heavy
# wasm toolchain and emscripten are fetched on first `qed build`, not here.
set -euo pipefail

REPO="https://github.com/JacobAsmuth/qed"
BRANCH="main"
QED_DIR="${HOME}/.qed"
SRC="${QED_DIR}/qed"
BIN="${QED_DIR}/bin"

info() { printf '\033[1m==> %s\033[0m\n' "$*"; }
err()  { printf '\033[31merror:\033[0m %s\n' "$*" >&2; exit 1; }

# 1. Lean toolchain (elan). The pinned toolchain installs automatically on first
#    `lake` run (elan reads lean-toolchain).
if ! command -v lake >/dev/null 2>&1 && [ ! -x "${HOME}/.elan/bin/lake" ]; then
  info "installing elan (Lean toolchain manager)"
  case "$(uname -sm)" in
    "Linux x86_64")   TRIPLE="x86_64-unknown-linux-gnu" ;;
    "Darwin arm64")   TRIPLE="aarch64-apple-darwin" ;;
    "Darwin x86_64")  TRIPLE="x86_64-apple-darwin" ;;
    *) err "unsupported platform $(uname -sm); install elan manually from https://github.com/leanprover/elan" ;;
  esac
  tmp="$(mktemp -d)"
  curl -sSfL "https://github.com/leanprover/elan/releases/latest/download/elan-${TRIPLE}.tar.gz" \
    | tar -xz -C "${tmp}"
  "${tmp}/elan-init" -y --default-toolchain none >/dev/null
  rm -rf "${tmp}"
fi
export PATH="${HOME}/.elan/bin:${PATH}"
command -v lake >/dev/null 2>&1 || err "lake not found after installing elan"

# 2. Fetch / update the framework.
if [ -d "${SRC}/.git" ]; then
  info "updating qed framework"
  git -C "${SRC}" pull --ff-only
else
  info "fetching qed framework"
  mkdir -p "${QED_DIR}"
  git clone --depth 1 --branch "${BRANCH}" "${REPO}" "${SRC}"
fi

# 3. Build the CLI (auto-installs the pinned Lean toolchain on first run).
info "building the qed CLI"
( cd "${SRC}" && lake build qed )

# 4. Install the launcher on PATH.
mkdir -p "${BIN}"
cat > "${BIN}/qed" <<'LAUNCH'
#!/usr/bin/env bash
export PATH="${HOME}/.elan/bin:${PATH}"
export QED_HOME="${HOME}/.qed/qed"
for e in "${HOME}/.qed/emsdk/emsdk_env.sh" "${HOME}/emsdk/emsdk_env.sh"; do
  [ -f "$e" ] && { . "$e" >/dev/null 2>&1; break; }
done
exec "${HOME}/.qed/qed/.lake/build/bin/qed" "$@"
LAUNCH
chmod +x "${BIN}/qed"

# 5. Ensure ~/.qed/bin is on PATH for future shells.
if ! printf '%s' ":${PATH}:" | grep -q ":${BIN}:"; then
  for rc in "${HOME}/.bashrc" "${HOME}/.zshrc" "${HOME}/.profile"; do
    [ -f "$rc" ] || continue
    grep -q '.qed/bin' "$rc" 2>/dev/null && continue
    printf '\n# qed\nexport PATH="%s:$PATH"\n' "${BIN}" >> "$rc"
  done
fi

info "qed installed"
echo "   Open a new shell (or run: export PATH=\"${BIN}:\$PATH\"), then:"
echo "     qed new myapp && cd myapp && qed dev"
