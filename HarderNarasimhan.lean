/-
Copyright (c) 2025-2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import HarderNarasimhan.Basic
import HarderNarasimhan.Interval

import HarderNarasimhan.Convexity.Defs
import HarderNarasimhan.Convexity.Results

import HarderNarasimhan.Semistability.Defs
import HarderNarasimhan.Semistability.Results
import HarderNarasimhan.Semistability.Translation

import HarderNarasimhan.Filtration.Defs
import HarderNarasimhan.Filtration.Results

import HarderNarasimhan.FirstMoverAdvantage.Results

import HarderNarasimhan.OrderTheory.DedekindMacNeilleCompletion

import HarderNarasimhan.SlopeLike.Defs

import HarderNarasimhan.NashEquilibrium.Defs
import HarderNarasimhan.NashEquilibrium.Results

import HarderNarasimhan.JordanHolderFiltration.Defs
import HarderNarasimhan.JordanHolderFiltration.Results

import HarderNarasimhan.CoprimaryFiltration.Defs
import HarderNarasimhan.CoprimaryFiltration.Results

/-!
# `HarderNarasimhan`: library root

This module is the umbrella import for the project. It re-exports the main definitions and the
public-facing results of each chapter.

API overview:

* Import `HarderNarasimhan` when you want the standard collection of definitions and theorems.
* For more granular dependencies, prefer importing individual `.../Defs` and `.../Results` modules.

API note: this file declares no new definitions/lemmas; it is purely a re-export layer.
-/
