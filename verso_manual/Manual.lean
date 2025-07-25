/-
 - Created in 2025 by Gaëtan Serré
-/

import VersoManual

import Manual.Front

open Verso.Genre.Manual Verso.Output.Html

def extraCss : List String := ["static/style.css"]

def extraHead : Array Verso.Output.Html := #[
    {{<link rel="icon" type="image/x-icon" href="static/favicon.svg"/>}},
    {{<script src="static/adjust_style.js"></script>}},
  ]

def config : Config :=
  Config.addKaTeX (
    Config.addSearch {
      extraCss := extraCss,
      extraHead := extraHead,
      sourceLink := some "https://github.com/gaetanserre/LipoCons",
      issueLink := some "https://github.com/gaetanserre/LipoCons/issues",
    }
  )

def main := manualMain (%doc Manual.Front) (config := config)
