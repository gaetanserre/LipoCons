/-
 - Created in 2025 by Gaëtan Serré
-/

import VersoManual

import Manual.Front

open Verso.Genre.Manual Verso.Output.Html

def extraHead : Array Verso.Output.Html := #[
    {{<link rel="icon" type="image/x-icon" href="static/favicon.svg"/>}},
    {{<link rel="stylesheet" href="static/style.css"/>}},
    {{<script src="static/scripts.js"></script>}},

  ]

def config : Config :=
  Config.addKaTeX (
    Config.addSearch {
      extraHead := extraHead,
      sourceLink := some "https://github.com/gaetanserre/LipoCons",
      issueLink := some "https://github.com/gaetanserre/LipoCons/issues",
    }
  )

def main := manualMain (%doc Manual.Front) (config := config)
