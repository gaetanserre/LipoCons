/-
 - Created in 2025 by Gaëtan Serré
-/

import VersoBlog
import VersoWebsite.Front
import VersoWebsite.Constant
import VersoWebsite.Theme
import VersoWebsite.ThmConsistency

set_option maxHeartbeats 0

open Verso Genre Blog Site Syntax

/- DEFS -/
def_literate_page def_algo_page
  from LipoCons.Defs.Algorithm in "src" as "Global optimization algorithms"

def_literate_page def_npos_page
  from LipoCons.Defs.NPos in "src" as "Positive integers"

def_literate_page def_lipschitz_page
  from LipoCons.Defs.Lipschitz in "src" as "Lipschitz functions"

def_literate_page def_consistency_page
  from LipoCons.Defs.Consistency in "src" as "Consistency"

/- UTILS -/

def_literate_page util_tuple_page
  from LipoCons.Utils.Tuple in "src" as "Utils -- Tuple"

def_literate_page util_tendsto_page
  from LipoCons.Utils.Tendsto in "src" as "Utils -- Tendsto"

def_literate_page util_metric_page
  from LipoCons.Utils.Metric in "src" as "Utils -- Metric"

def_literate_page util_indistinguishable_page
  from LipoCons.Utils.Indistinguishable in "src" as "Indistinguishable function"

def_literate_page util_fintype_page
  from LipoCons.Utils.Fintype in "src" as "Utils -- Fintype"

def_literate_page util_finset_page
  from LipoCons.Utils.Finset in "src" as "Utils -- Finset"

def_literate_page util_ennreal_page
  from LipoCons.Utils.ENNReal in "src" as "Utils -- ENNReal"

def_literate_page util_ecover_page
  from LipoCons.Utils.ECover in "src" as "ε-cover of a compact space"

def_literate_page util_compact_page
  from LipoCons.Utils.Compact in "src" as "Utils -- Compact"

def demoSite : Site := site VersoWebsite.Front /
  static "static" ← "verso_website/static_files"
  "Algorithm" def_algo_page
  "Lipschitz" def_lipschitz_page
  "Consistency" def_consistency_page
  "Indistinguishable" util_indistinguishable_page
  "Theorem" VersoWebsite.ThmConsistency
  "Compact" util_compact_page
  "NPos" def_npos_page
  "ECover" util_ecover_page
  "Tuple" util_tuple_page
  "Fintype" util_fintype_page
  "Finset" util_finset_page
  "ENNReal" util_ennreal_page
  "Metric" util_metric_page
  "Tendsto" util_tendsto_page

def main := blogMain theme demoSite
