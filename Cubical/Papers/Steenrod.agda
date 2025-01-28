{-

Please do not move this file. Changes should only be made if necessary.

This file contains pointers to the code examples and main results from
the paper:

The Steenrod squares via unordered joins

-}


-- The "--safe" flag ensures that there are no postulates or unfinished goals
{-# OPTIONS --safe #-}


open import Cubical.HITs.RPn.Base                                         as RP

open import Cubical.Cohomology.EilenbergMacLane.Steenrod.Base             as Def
open import Cubical.Cohomology.EilenbergMacLane.Steenrod.MasterTheorem    as Master
open import Cubical.HITs.RPn.Unordered                                    as Unordered
open import Cubical.HITs.RPn.JoinFubini                                   as Fubini

module Cubical.Papers.Steenrod where

-- II. UNORDERED PAIRS AND COMMUTATIVITY STRUCTURES

-- Implementations of RP∞ (differs slightly from paper in order to
-- make certain computation rules definitional)
open RP using (RP∞')

-- Versions of lemmas 2-7 can be found in
open RP
-- (and were already well-known)

-- Definitions 8 and 12 (Commutativity structures) is only implicitly used

-- Example 9 (for ℕ). Example 10 only included for pedagogical reasons and is never used.
open Def using (∑RP∞')

-- Definition 11 is omitted as this is not the definition we used (we use unordered joins)

-- Definition 14 (unordered cup product)
open Def using (S)

-- II. THE STEENROD SQUARES

-- Lemma 15
open Def using (RP→EM-ℤ/2-CharacIso'-expl')

-- Definition 18: (Total) Steenrod squares
open Def using (SqTot ; Sq)

-- For the properties, we have focused on the master theorem (Theorem
-- 20) and omitted the elementary algebraic proofs following it.
open Master using (S-MasterTheorem)

-- Nevertheless, here's a (generalised) version of the Cartan formula (equation 4)
open Master using (S-Cartan)

-- IV. THE ZEROTH SQUARE


-- V. UNORDERED JOINS AND THEIR FUBINI THEOREM
-- The Fubini theorem (Lemma 35)
open Fubini using (UnordJoinFubiniFun)
-- Note that this is not the while proof: it also makes up most of the following file
open Unordered
