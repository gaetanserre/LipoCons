# LipoCons

[![CI](https://github.com/gaetanserre/LipoCons/actions/workflows/build_verso_doc.yml/badge.svg)](https://github.com/gaetanserre/LipoCons/actions/workflows/build_verso_doc.yml)

This repository contains the Lean formalization of the Proposition 3 of the the paper [*_Global optimization of Lipschitz functions, Malherbe C. and Vayatis N., 2017_*](https://proceedings.mlr.press/v70/malherbe17a/malherbe17a.pdf). It uses [LeanGO](https://github.com/gaetanserre/LeanGO) for a formal definition of global optimization algorithms.

## Usage
Install [Lean 4](https://lean-lang.org/install/). Then, clone the repository and run the following command in the root directory:

```bash
lake exe cache get
lake build
```
Now you can explore the proof using your favorite editor with Lean support, such as [VSCode](https://code.visualstudio.com/) with the [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4).

## Documentation
The documentation is available [here](https://gaetanserre.fr/doc/LipoCons/). To build it, clone the repository and run the following command in the root directory:

```bash
lake exe cache get
lake build
cd doc
./build_manual.sh
```
The documentation will be generated in the `html` directory. You will need a local web server to view the documentation. You can use Python's built-in HTTP server:

```bash
cd doc/html
python3 -m http.server
```
and open your web browser at `http://localhost:8000`.