# Build HTML documentation for add-combi
# The output will be located in docs/build

# Template lakefile.toml
template() {
  cat <<EOF
name = "docbuild"
reservoir = false
version = "0.1.0"
packagesDir = "../.lake/packages"

[[require]]
name = "FLT"
path = "../"

[[require]]
scope = "leanprover"
name = "doc-gen4"
rev = "TOOLCHAIN"
EOF
}

# Create a temporary docbuild folder
mkdir -p docbuild

# Equip docbuild with the template lakefile.toml
template > docbuild/lakefile.toml

# Substitute the toolchain from lean-toolchain into docbuild/lakefile.toml
sed -i s/TOOLCHAIN/`grep -oP 'v4\..*' lean-toolchain`/ docbuild/lakefile.toml

# Initialise docbuild as a Lean project
cd docbuild
~/.elan/bin/lake update AddCombi
~/.elan/bin/lake exe cache get

# Build the docs
~/.elan/bin/lake build AddCombi:docs

# Move them out of docbuild
cd ../
mv docbuild/.lake/build/doc docs/build

# Clean up after ourselves
rm -rf docbuild
