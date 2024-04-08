/-
  This module serves as the root of the `LeanRaskell` library. Import modules here that should be built as part of the library.
-/
import LeanRaskell.Core
import Std

/--
  A `Token` in a `Sequence` is a small integer.
  RASP-L uses `UInt8` to ensure all maps of type `Token` -> `Token` are learnable.
-/
abbrev Token := UInt8

instance : Coe Token Nat where
  coe := UInt8.toNat

instance : CoeDep Nat n Token where
  coe := UInt8.ofNat n

def Token.min : Token := 0
def Token.max : Token := 255

@[inherit_doc List]
abbrev Sequence := List Token
abbrev Keys := List Token
abbrev Values := List Token
abbrev Queries := List Token
abbrev BoolSequence := List Bool
/-- Takes 2 tokens and decides their equality. -/
abbrev Predicate := Token → Token → Bool
/--
  A `Selector` is a list of lists of booleans.
  It represents a binary attention matrix used in the `selectCausal` function.
-/
abbrev Selector := List (List Bool)

inductive AggregationType where
  | min
  -- | mean
  | max


def Array.join : Array (Array α) → Array α := .foldl .append .empty
declare_syntax_cat compClause
syntax "for " term " in " term : compClause
syntax "if " term : compClause

syntax "[" term " | " compClause,* "]" : term
syntax "#[" term " | " compClause,* "]" : term
macro_rules
  | `([$t:term |]) => `([$t])
  | `([$t:term | for $x in $xs]) => `(List.map (λ $x => $t) $xs)
  | `([$t:term | if $x]) => `(if $x then [$t] else [])
  | `([$t:term | $c, $cs,*]) => `(List.join [[$t | $cs,*] | $c])

macro_rules
  | `(#[$t:term |]) => `(#[$t])
  | `(#[$t:term | for $x in $xs]) => `(($xs).map (λ $x ↦ $t))
  | `(#[$t:term | if $x]) => `(if $x then #[ $t ] else #[])
  | `(#[$t:term | $c, $cs,*]) => `(Array.join #[#[$t | $cs,*] | $c ])


#eval [(x, y) | for x in List.range 5, for y in List.range 5, if x + y <= 3]

def List.prod (xs : List α) (ys : List β) : List (α × β) := [(x, y) | for x in xs, for y in ys]

def Array.prod (xs : Array α) (ys : Array β) : Array (α × β) := #[ (x, y) | for x in xs, for y in ys ]


#eval #[#[1],#[1,2]].join
#eval #[x+1| for x in #[1,2,3]]
#eval #[#[2],#[3]]|>.join
-- #[2, 3, 4]
#eval #[4 | if 1 < 0]
-- #[]
#eval #[4 | if 1 < 3]
-- #[4]
#eval #[(x, y) | for x in Array.range 5, for y in Array.range 5, if x + y <= 3]
-- #[(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (3, 0)]

instance [Inhabited α] : Inhabited (Option α) where
  default := none

/--
  Unwraps an option, returning the contained value if it is `some`, or a default value if it is `none`.
-/
def Option.unwrapOr [Inhabited α] (val: Option α) (default : α := Inhabited.default) : α :=
  if let some v := val then v else default

namespace List
/-- Construct a new empty list. -/
def empty: List a := []
def sum [Add a][Inhabited a] (xs: List a): a := xs.foldr (· + · ) default

def mean? (xs:  Sequence): Option Float :=
  if xs.isEmpty then none
  else some (xs.sum / xs.length)
#eval [1,2,3,8].mean?

def max! [Max a][Inhabited a] : List a → a := (·.maximum?.get!)
def min! [Min a][Inhabited a] : List a → a := (·.minimum?.get!)
def mean! [Add a][Inhabited a][HDiv a Nat a]: List a → a := (·.mean?.get!)
#eval [2,5].mean!
/--
  Filters a list of values based on a list of booleans.
-/
def filterBy : List a -> List Bool -> List a
| (x :: xs), (true :: bs) => x :: xs.filterBy bs
| (_ :: xs), (false :: bs) => xs.filterBy bs
| _, _ => []
#eval [1,2,3].filterBy [true, false, true] = [1, 3]
end List



abbrev Aggregator := Selector -> Values -> Sequence


-- theorem minMeanMaxTheorem (xs: List Nat) (h: xs.length > 0) : xs.min! ≤ xs.mean! ∧ xs.mean! ≤ xs.max!:=
--   let filteredValues := values.filterBy mask
--   let minVal := filteredValues.min?
--   let meanVal := filteredValues.mean?
--   let maxVal := filteredValues.max?

--   minVal ≤ meanVal ∧ meanVal ≤ maxVal ∧ meanVal.isNat
-- TODO restore mean

/--
  Finds the maximum value in a sequence.
-/
def aggrMaxByRow  (filler:Token) (values: Sequence ) (mask: BoolSequence): Token :=
  (values.filterBy mask).maximum?.unwrapOr filler
/--
  Finds the minimum value in a sequence.
-/
def aggrMinByRow  (filler:Token) (values: Sequence ) (mask: BoolSequence): Token :=
  (values.filterBy mask).minimum?.unwrapOr filler
-- def aggrMeanByRow  (filler: Token) (values: Sequence) (mask: BoolSequence) : Token :=
--   (values.filterBy mask).mean?.unwrapOr filler
-- TODO replace Option with NonEmptyList
/--
  Creates an aggregator with a given aggregation type.
-/
def aggregate  (agg: AggregationType): Token -> Selector -> Values -> Sequence :=
  match agg with
    | .max => aggrMaxByRow
    -- | .mean => aggrMeanByRow
    | .min => aggrMinByRow

  -- λ filler (bs:BoolSequence) v => (aggregator filler v).map bs
  --   where
  --     aggregator := match agg with
  --       | .max => aggrMaxByRow
  --       -- | .mean => aggrMeanByRow
  --       | .min => aggrMinByRow

/--
  Non-causal selection is included for some reason.
-/
def selectAcausal : Keys -> Queries -> Predicate -> Selector :=
  fun keys queries predicate =>
    [ [predicate keyIndex queryIndex | for keyIndex in keys] | for queryIndex in queries]


/--
  Compares pairs of elements from sequences with a predicate subject to a causal constraint using list comprehension notation.
-/
def selectCausal (keys: Keys) (queries: Queries) (predicate: Predicate) : Selector :=
  [ [ (keyIndex <= queryIndex) && predicate (keys.get! keyIndex) (queries.get! queryIndex)
      | for keyIndex in [0:keys.length] ]
    | for queryIndex in [0:queries.length] ]

/--
  Performs a key-query-value lookup operation and aggregates over values.

  Given a filler token, an aggregation type, two sequences (keys and queries),
  and a predicate, it returns a processed sequence. It first selects elements
  based on the predicate and then aggregates them.

  Roughly matches the attention layer of a Transformer.
-/
def kqv
  -- Filler token used in aggregation
  (filler:Token)
  -- Type of aggregation (Min, Mean, Max)
  (aggr:AggregationType)
  -- Sequence of keys
  (keys:Keys)
  -- Sequence of queries
  (queries:Queries)
  -- A boolean predicate that determines whether a key and query match
  (pred:Predicate)
  -- Sequence of values
  (vals:Values)
  -- The output sequence
  Sequence :=
  aggregate aggr filler (selectCausal keys queries predicate)

/--
  Performs Key-Query-Value lookup with maximum aggregation of values.
-/
def maxKQV (k: Keys) (q: Queries) (p:Predicate)  (v:Values) : Sequence:=
  kqv Int8.min AggregationType.max k q p v
#eval [0:3-1]
#eval [1,2].minimum?
/--
  Performs Key-Query-Value lookup with minimum aggregation of values.
-/
def minKQV (k: Keys) (q: Queries) (p:Predicate)  (v:Values) : Sequence:=
  kqv Int8.max AggregationType.min k q p v

#eval [0:3].toArray

def Std.Range.foldr (r:Std.Range) (init : α) (f : Nat → α → α) : α :=
  Id.run do
    let mut result := init
    for x in r do
      result := f x result
    return result

-- TODO generalize Std.Range and put in PR
-- def Std.Range.reverse (r:Std.Range) : Std.Range :=
--   [r.stop: r.start: -1]

def Std.Range.foldl (r:Std.Range) (init : α) (f : Nat → α → α) : α := r.foldr init f

def Std.Range.sum (r:Std.Range) : Nat := r.foldr 0 .add
#eval [0:7].sum
def Std.Range.toArray (r:Std.Range): Array Nat := Id.run do
  let mut result: Array Nat := #[]
  for x in r do
    result := result.push x
  return result


instance : Coe Std.Range (Array Nat) where
  coe := Std.Range.toArray

instance : Coe Std.Range (List Nat) where
  coe r := Id.run do
    let mut result: List Nat := []
    for x in r do
      result := x :: result
    return result
def Std.Range.toList (r:Std.Range) : List Nat := r.toArray.toList

#eval [0:3].toList
/--
  Constructs a causal binary attention matrix based on the given keys, queries, and predicate.
-/
def selectCausal (keys: Keys)  (queries:Queries)  (predicate:Predicate) : Selector:=
  [ [ (keyIndex <= queryIndex) && predicate (keys.get keyIndex) (queries.get! queryIndex)
    | for keyIndex in [0:keys.length - 1]
    ]
    | for queryIndex in [0:queries.length - 1]
  ]

/--
  Creates a matched-length constant sequence with the provided token.
-/
def filledWith : Sequence -> Token -> Sequence
filledWith = replicate . length

/--
  Extracts the indices of the elements in a sequence.
-/
def indicesOf : Sequence -> Sequence
indicesOf x := [0 .. (fromIntegral (length x) - 1)]

/-
  Type alias for "fully-specified" aggregators that are ready to aggregate a sequence of values with a selector.
-/


-- FILEPATH: /Users/alokbeniwal/lean_raskell/LeanRaskell.lean
#eval ([1, 4, 2, 10, 6].maximum?) = some 10

/-- TODO generalize to any additive monoid -/

#eval [1].maximum
#eval List.maximum? [1,2,3]
def List.maximum? : List Nat → Option Nat := (·.maximum)
-- FILEPATH: /Users/alokbeniwal/lean_raskell/LeanRaskell.lean
-- BEGIN: ed8c6549bwf9



/--
  Computes the "width", or number of nonzero entries, of the rows of a `Selector`.
-/
-- def selWidth : Selector -> Sequence := map (sum . map fromBool)
def selWidth (selector: Selector) : Sequence :=
  selector.map fun row => row.map fun b => if b then 1 else 0 |>.sum
/--
  Converts a boolean value to a token.
-/
instance : Coe Bool Token where
  coe
    | false => 0
    | true => 1
/--
  Applies an elementwise operation to a sequence of tokens.
-/
def tokMap : (Token -> Token) -> Sequence -> Sequence := map

/--
  Applies an elementwise operation for pairs of tokens on a pair of sequences.
-/
def seqMap : (Token -> Token -> Token) -> Sequence -> Sequence -> Sequence := zipWith


/--
  Creates a sequence of the same length as the provided sequence filled with the provided token.
-/

def full := filledWith

/--
  Extracts the indices of the elements in a sequence.
-/

def indices := indicesOf


@[inherit_doc aggregate]
def aggr := aggregate



#eval [(x, y) | for x in List.range 5, for y in List.range 5, if x + y <= 3]

/--
  Produces a selector indicating which pairs of `Keys` and `Queries` match.
-/
def select
  -- Whether to use causal selection
  (causal: Bool):
  -- A collection of `Keys` to check against `Queries`
  Keys ->
  -- A collection of `Queries` to check against `Keys`
  Queries ->
  -- A boolean predicate that determines whether a key and query match
  Predicate ->
  -- A collection of boolean sequences indicating which pairs of `Keys` and `Queries` match
  Selector:=
    if causal then selectCausal else selectAcausal


structure Place where
  lat: Float
  lon: Float
