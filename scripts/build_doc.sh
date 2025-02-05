# Buid HTML documentation for add-combi
# The output will be located in docs/build

# Template lakefile.toml
template() {
  cat <<EOF
name = "docbuild"
reservoir = false
version = "0.1.0"
packagesDir = "../.lake/packages"

[[require]]
name = "AddCombi"
path = "../"

[[require]]
scope = "leanprover"
name = "doc-gen4"
rev = "TOOLCHAIN"
EOF
}

# Create docbuild
mkdir -p docbuild

# Print the template to docbuild/lakefile.toml
template > docbuild/lakefile.toml

# Substitute the toolchain from lean-toolchain into docbuild/lakefile.toml
sed -i s/TOOLCHAIN/`grep -oP 'v4\..*' lean-toolchain`/ docbuild/lakefile.toml

# Initialise `docbuild` as a repository
cd docbuild
lake update AddCombi
lake exe cache get

# Build the docs
lake build AddCombi:docs

cd ../

# Move them out of the temporary docbuild folder
mv docbuild/.lake/build/doc docs/build

# Clean up after ourselves
rm -rf docbuild
