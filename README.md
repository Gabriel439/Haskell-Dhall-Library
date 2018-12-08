# `dhall-haskell`

You will probably want to read the language-agnostic `README` here:

* [`dhall-lang` `README`](https://github.com/dhall-lang/dhall-lang/blob/master/README.md)

This repository focuses on the Haskell bindings to Dhall and contains
the following packages:

* [`dhall`](./dhall) - [![Hackage](https://img.shields.io/hackage/v/dhall.svg)](https://hackage.haskell.org/package/dhall)
* [`dhall-bash`](./dhall-bash) - [![Hackage](https://img.shields.io/hackage/v/dhall-bash.svg)](https://hackage.haskell.org/package/dhall-bash)
* [`dhall-json`](./dhall-json) - [![Hackage](https://img.shields.io/hackage/v/dhall-json.svg)](https://hackage.haskell.org/package/dhall-json)
* [`dhall-text`](./dhall-text) - [![Hackage](https://img.shields.io/hackage/v/dhall-text.svg)](https://hackage.haskell.org/package/dhall-text)

Navigate to each package's directory for their respective `README`s

## Building from source

### [cabal](https://www.haskell.org/cabal)

You can build all of the packages by running:

```console
$ cabal new-build all
```

And each of them with `cabal new-build <package-name>`, for example:

```console
$ cabal new-build dhall
```

... or you can run `cabal new-build` within each package directory.

### [nix](https://nixos.org/nix/)

You can build all of the packages by running:

```console
$ nix-build
```

... or you can run `nix-build` within each package's respective directory to
build just that one package.

You can install all of the packages by running:

```
$ nix-env --install --file default.nix
```

... or you can run the same command within each package's respective directory
to install just that one package.

You can develop any package by navigating to that package's directory and
running:

```bash
$ nix-shell
[nix-shell]$ cabal configure
[nix-shell]$ cabal build
[nix-shell]$ cabal test
```

... or you can add `nix: True` to your `~/.cabal/config` file and then you can
run the same `cabal` commands without an explicit `nix-shell`:

```bash
$ cabal configure
$ cabal build
$ cabal test
```

### [stack](https://docs.haskellstack.org)

You can build all of the packages with

```console
$ stack build
```

And each of them with `stack build <package-name>`, for example:

```console
$ stack build dhall-json
```

## Build and serve the "Try Dhall" website

This is currently only supported for Nix on Linux

You can build the static assets by running:

```bash
$ nix-build --attr try-dhall-static
```

For local testing you can open the generated `./result/index.html` directly in
your browser and everything will work except for relative imports of the
Prelude.

To also test imports you can build the `try-dhall-server` script which uses
`warp` to serve the static assets:

```bash
$ nix-build --attr try-dhall-server
$ result/bin/try-dhall-server
Serving directory /nix/store/i7x86qs888rndrhvw92y69jd5xaji060-try-dhall-static on port 3000 with ["index.html","index.htm"] index files.
```

... and then open `http://localhost:3000` in your browser.  You will then be
able to import things from the Prelude within your Dhall configuration using
a path like `http://localhost:3000/Prelude/List/map`.  Similarly, if you host
this on some public-facing domain such as `https://try.dhall-lang.org` then you
can import the Prelude using `https://try.dhall-lang.org/Prelude/List/map`.

Note that imports from other domains (such as `prelude.dhall-lang.org`) will not
yet work since cross-origin resource-sharing (CORS) is not enabled.  This is why
the "Try Dhall" server serves its own copy of the Prelude.

## Contributing

Read the following guide if you would like to contribute:

* [Contributing to Dhall](https://github.com/dhall-lang/dhall-lang/blob/master/.github/CONTRIBUTING.md)
