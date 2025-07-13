-- This module serves as the root of the `StoneDuality` library.
-- Import modules here that should be built as part of the library.

-- Basic definitions, some are a little janky but provide an abstract interface.
import StoneDuality.Basic
import StoneDuality.DirSet

-- Definitions of the two types of dcpos we consider and proofs of some basic properties
import StoneDuality.Dcpo

-- Properties about the ideal completion of a poset P
import StoneDuality.IdealCompletion

-- Compactness properties and algebraic dcpos
import StoneDuality.Compact

-- Definition of Scott continuity and basic properties
import StoneDuality.ScottCont

import StoneDuality.Lift
