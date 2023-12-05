-- This module serves as the root of the `LeanRaskell` library.
-- Import modules here that should be built as part of the library.
import «LeanRaskell».Core
#print inferInstance

structure  Point (a:Type u) [Inhabited a] where
  x : a := default
  y : a := default
  z : a := default
deriving Repr
structure RGBValue where
  red : Nat := default
  green : Nat := default
  blue : Nat := default
deriving Repr
structure RedGreenPoint (a:Type) [Inhabited a] extends Point a, RGBValue where
  no_blue : blue = 0 := by simp
deriving Repr
-- FILEPATH: /Users/alokbeniwal/lean_raskell/LeanRaskell.lean
-- BEGIN: rgbpoint-inhabited-instance


instance [Inhabited a] : Inhabited (RedGreenPoint a) :=
  ⟨{ x := default, y := default, z := default, red := default, green := default, blue := default ,no_blue:= by rfl}⟩
-- END: rgbpoint-inhabited-instance

def aaa:RedGreenPoint Int := {x := 1, y:=2,z:=3,red:=1,blue:=1-1+1-2,green:=3}
#eval aaa


def Int8 := {n:Int // -128 ≤ n ∧ n < 128 }
def Int8.min:Int8 := -128
def Int8.max:Int8 := 127
-- instance : OfNat Int8 (n:Nat) (128>n ∧ n >=-128) :=
--   ⟨n, by decide⟩
instance : OfNat Int8 127 :=
  ⟨127, by trivial⟩
-- | A `Token` in a `Sequence` is a small integer.
-- RASP-L uses `Int8` to ensure all maps of type `Token` -> `Token` are learnable.

def Token := UInt8 -- TODO do Int8
def Sequence:= List Token
def Keys := List Token
def Values := List Token
def Queries := List Token
def Predicate := Token → Token → Bool

def Selector := List (List Bool)
def BoolSequence := List (Bool)


inductive AggType:= |min|mean|max

-- | Performs a key-query-value lookup operation and aggregates over values.
--
-- Given a filler token, an aggregation type, two sequences (keys and queries),
-- and a predicate, it returns a processed sequence. It first selects elements
-- based on the predicate and then aggregates them.
--
-- Roughly matches the attention layer of a Transformer.
def kqv
  -- | Filler token used in aggregation
  (filler:Token)
  -- | Type of aggregation (Min, Mean, Max)
  (aggr:AggregationType)
  -- | Sequence of keys
  (keys:Keys)
  -- | Sequence of queries
  (queries:Queries)
  -- | A boolean predicate that determines whether a key and query match
  (pred:Predicate)
  -- | Sequence of values
  (vals:Values)
  -- | The output sequence
  (out: Sequence):=
  aggregate agg filler $ selectCausal keys queries predicate


-- | Performs Key-Query-Value lookup with maximum aggregation of values.
def maxKQV (k: Keys) (q: Queries) (p:Predicate)  (v:Values) : Sequence:=
  kqv Int8.min Max

def minKQV (k: Keys) (q: Queries) (p:Predicate)  (v:Values) : Sequence:=
  kqv Int8.max Min


def select(k:Keys) (q:Queries)( pred:Predicate):= do
-- constructs a causal binary attention matrix

let s := k.length
-- scilean array
A = np.zeros((s, s), dtype=bool)
for i in range(s):
for j in range(i+1):
A[i, j] = pred(k[j], q[i])
return A


-- | Compareis pairs of elements from sequences with a predicate subject to a causal constraint.
def selectCausal (keys: Keys)  (queries:Queries)  (predicate:Predicate) : Selector:=
  [ [ (keyIndex <= queryIndex) && predicate (keys !! keyIndex) (queries !! queryIndex)
      | keyIndex <- [0 .. length keys - 1]
    ]
    | queryIndex <- [0 .. length queries - 1]
  ]

-- | Creates a matched-length constant sequence with the provided token.
filledWith :: Sequence -> Token -> Sequence
filledWith = replicate . length

-- | Extracts the indices of the elements in a sequence.
indicesOf :: Sequence -> Sequence
indicesOf x = [0 .. (fromIntegral (length x) - 1)]

-- | Type alias for "fully-specified" aggregators that are ready to aggregate a sequence of values with a selector.
type Aggregator = Selector -> Values -> Sequence

-- | Aggregates values with some aggregation, filling in with a default token.
aggregate :: AggregationType -> Token -> Aggregator
aggregate Max = aggrMax
aggregate Mean = aggrMean
aggregate Min = aggrMin

#eval [1].minimum?
def aggregate :=

-- | Aggregates values by selecting the largest value.
aggrMax :: Token -> Aggregator
aggrMax filler a v = map (aggrMaxByRow filler v) a

-- | Aggregates values by taking the mean.
aggrMean :: Token -> Aggregator
aggrMean filler a v = map (aggrMeanByRow filler v) a

-- | Aggregates values by selecting the smallest value.
aggrMin :: Token -> Aggregator
aggrMin filler a v = map (aggrMinByRow filler v) a

aggrMaxByRow :: Token -> Sequence -> BoolSequence -> Token
aggrMaxByRow filler v a = fromMaybe filler maybeMax
  where
    maybeMax = safeMaximum (filterByList a v)

aggrMeanByRow :: Token -> Sequence -> BoolSequence -> Token
aggrMeanByRow filler v a = fromMaybe filler maybeMean
  where
    maybeMean = safeInt8Mean (filterByList a v)

aggrMinByRow :: Token -> Sequence -> BoolSequence -> Token
aggrMinByRow filler v a = fromMaybe filler maybeMin
  where
    maybeMin = safeMinimum (filterByList a v)

filterByList :: [Bool] -> [a] -> [a]
filterByList (True : bs) (x : xs) = x : filterByList bs xs
filterByList (False : bs) (_ : xs) = filterByList bs xs
filterByList _ _ = []

safeMaximum :: (Ord a) => [a] -> Maybe a
safeMaximum [] = Nothing
safeMaximum xs = Just (maximum xs)

safeMinimum :: (Ord a) => [a] -> Maybe a
safeMinimum [] = Nothing
safeMinimum xs = Just (minimum xs)

safeInt8Mean :: Sequence -> Maybe Token
safeInt8Mean [] = Nothing
safeInt8Mean xs = Just (sum xs `div` fromIntegral (length xs))

-- | Computes the "width", or number of nonzero entries, of the rows of a `Selector`.
selWidth :: Selector -> Sequence
selWidth = map (sum . map fromBool)

fromBool :: Bool -> Token
fromBool True = 1
fromBool _ = 0

-- | Applies an elementwise operation to a sequence of tokens.
--
-- Roughly matches the MLP layer in a Transformer. Alias for `map`.
tokMap :: (Token -> Token) -> Sequence -> Sequence
tokMap = map

-- | Applies an elementwise operation for pairs of tokens on a pair of sequences.
-- Alias for `zipWith`.
seqMap :: (Token -> Token -> Token) -> Sequence -> Sequence -> Sequence
seqMap = zipWith

-- | Creates a sequence of the same length as the provided sequence filled with the provided token.
-- Alias for `filledWith`.
full :: Sequence -> Token -> Sequence
full = filledWith

-- | Extracts the indices of the elements in a sequence.
-- Alias for `indicesOf`.
indices :: Sequence -> Sequence
indices = indicesOf

-- | Creates an aggregator with a given aggregation type.
-- Alias for `aggregate`.
aggr :: AggregationType -> Token -> Aggregator
aggr = aggregate

-- | Produces a selector indicating which pairs of `Keys` and `Queries` match.
select ::
  -- | Whether to use causal selection
  Bool ->
  -- | A collection of `Keys` to check against `Queries`
  Keys ->
  -- | A collection of `Queries` to check against `Keys`
  Queries ->
  -- | A boolean predicate that determines whether a key and query match
  Predicate ->
  -- | A collection of boolean sequences indicating which pairs of `Keys` and `Queries` match
  Selector
select True = selectCausal
select False = selectAcausal

-- | Non-causal selection is included for some reason.
selectAcausal :: Keys -> Queries -> Predicate -> Selector
selectAcausal keys queries predicate = [[predicate keyIndex queryIndex | keyIndex <- keys] | queryIndex <- queries]
