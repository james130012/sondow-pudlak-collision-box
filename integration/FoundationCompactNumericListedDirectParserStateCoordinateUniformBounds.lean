import integration.FoundationCompactNumericListedDirectParserStateFormula

/-!
# Uniform public bounds for parser-state coordinates

The eight fields of a parser-state row are exposed as one finite vector.  The
two predicates below are transparent abbreviations for coordinatewise numeric
and binary-length bounds; they carry no certificate or proof resource.
-/

namespace FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds

open FoundationCompactNumericListedDirectParserStateFormula

def compactUnifiedParserStateCoordinateValues
    (coordinates : CompactUnifiedParserStateRowCoordinates) : Fin 8 -> Nat :=
  ![coordinates.start, coordinates.finish, coordinates.tokensFinish,
    coordinates.tasksFinish, coordinates.tokensBoundary,
    coordinates.tokensCount, coordinates.tasksBoundary,
    coordinates.tasksCount]

def CompactUnifiedParserStateCoordinateValueBound
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (numericBound : Nat) : Prop :=
  forall coordinate,
    compactUnifiedParserStateCoordinateValues coordinates coordinate <=
      numericBound

def CompactUnifiedParserStateCoordinateSizeBound
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (bitBound : Nat) : Prop :=
  forall coordinate,
    Nat.size
      (compactUnifiedParserStateCoordinateValues coordinates coordinate) <=
        bitBound

end FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
