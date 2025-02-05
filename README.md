# add-combi

![GitHub CI](https://github.com/YaelDillies/add-combi/workflows/continuous%20integration/badge.svg?branch=master)
[![project chat](https://img.shields.io/badge/zulip-join_chat-brightgreen.svg)](https://leanprover.zulipchat.com)
[![Gitpod Ready-to-Code](https://img.shields.io/badge/Gitpod-ready--to--code-blue?logo=gitpod)](https://gitpod.io/#https://github.com/YaelDillies/add-combi)

[add-combi](https://yaeldillies.github.io/add-combi) is a user-maintained library for the [Lean theorem prover](https://leanprover.github.io)
destined to cover [additive combinatorics](https://en.wikipedia.org/wiki/Additive_combinatorics).

It builds on [mathlib](https://leanprover-community.github.io) and follows its documentation,
contribution and style guidelines.

## Installation

You can find detailed instructions to install Lean, mathlib, add-combi, and supporting tools on
[our website](https://leanprover-community.github.io/get_started.html). Alternatively, click on one
of the buttons below to open a GitHub Codespace or a Gitpod workspace containing the project.

[![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/YaelDillies/add-combi)

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/YaelDillies/add-combi)

## Experimenting

Got everything installed? Why not start with the [tutorial project](https://leanprover-community.github.io/install/project.html)?

For more pointers, see [Learning Lean](https://leanprover-community.github.io/learn.html).

## Documentation

Besides the installation guides above and
[Lean's general documentation](https://docs.lean-lang.org/lean4/doc/), the documentation of
add-combi consists of:
* [The add-combi docs](https://yaeldillies.github.io/add-combi/index.html): documentation
  [generated automatically](https://github.com/leanprover/doc-gen4) from the source `.lean` files.
* Some [extra Lean documentation](https://leanprover-community.github.io/learn.html) not specific to
  add-combi (see "Miscellaneous topics").
* Documentation for people who would like to [contribute](https://leanprover-community.github.io/contribute/index.html).

Much of the discussion surrounding Lean, mathlib and add-combi occurs in a
[Zulip chat room](https://leanprover.zulipchat.com/), and you are welcome to join, or read along
without signing up. Questions from users at all levels of expertise are welcome!

## Contributing

add-combi follows [the same contribution guide as mathlib](https://leanprover-community.github.io/contribute/index.html).

The process is different from other projects where one should not fork the repository.
Instead write permission for non-master branches should be requested on [Zulip](https://leanprover.zulipchat.com)
by introducing yourself, providing your GitHub handle and what contribution you are planning on doing.
You may want to subscribe to the `mathlib4` stream

* To obtain precompiled `olean` files, run `lake exe cache get`.
  (Skipping this step means the next step will be very slow.)
* To build `AddCombi` run `lake build`.
* You can use `lake build AddCombi.Import.Path` to build a particular file, e.g.
  `lake build AddCombi.DiscreteAnalysis.Convolution.Defs`.
* If you add a new file, run the following command to update `AddCombi.lean`

  ```shell
  lake exe mk_all
  ```

### Guidelines

add-combi follows the same guidelines and conventions as mathlib:
*-* The [style guide](https://leanprover-community.github.io/contribute/style.html)
*-* A guide on the [naming convention](https://leanprover-community.github.io/contribute/naming.html)
*-* The [documentation style](https://leanprover-community.github.io/contribute/doc.html)

### Downloading cached build files

You can run `lake exe cache get` to download cached build files that are computed by mathlib's
automated workflow. Note that no cache is available to download for add-combi for the time being.

If something goes mysteriously wrong, you can try one of `lake clean` or `rm -rf .lake` before
trying `lake exe cache get` again.

Call `lake exe cache` to see its help menu.

### Building HTML documentation

The docs are generated using `scripts/build_doc.sh` (run it from the root directory). It may take a
while (>20 minutes). The HTML files can then be found in `docs/build`.

### Dependencies

If you are an add-combi contributor and want to update dependencies, use `lake update`.
This will update the `lake-manifest.json` file correctly.
You will need to make a PR after committing the changes to this file.

## Maintainers:

* Yaël Dillies (@YaelDillies)
* Bhavik Mehta (@b-mehta)
