


DeclareOperation("SplitByCentre", [IsUTable]);
DeclareOperation("SplitByCentre", [IsUTable, IsList]);
DeclareAttribute("SplittingCentre", IsUTable);
DeclareOperation("SplitCharactersByCentre", 
                        [IsUTable and HasSplittingCentre, IsList]);
