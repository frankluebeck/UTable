###########################################################################
##  UTable.gd
##  
##  (C) 2025 Frank Lübeck, Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen
##  
##  These files contains functions to create a UTable for a finite group.
##  This will be used as a container for computing the irreducible characters
##  of the group without using 'CharacterTable'.
##  

##  Filter for partial character tables that can be completed interactively
##  and with the Unger algorithm (induction from elementary subgroups and LLL
##  reduction).
DeclareFilter("IsUTable", IsComponentObjectRep and IsAttributeStoringRep and IsNearlyCharacterTable);
DeclareAttribute("UTable", IsGroup, "mutable");
BindGlobal("UTableType", NewType(NearlyCharacterTablesFamily, IsUTable));

# missing in GAP library
DeclareAttribute("NrRationalClasses", IsGroup);
DeclareAttribute("NrRationalClasses", IsNearlyCharacterTable);

DeclareAttribute("RationalClassIndices", IsGroup);
DeclareAttribute("RationalClassIndices", IsNearlyCharacterTable);

DeclareGlobalName("ImportToUTable");
DeclareGlobalName("ExtendGramUTable");
DeclareGlobalName("ReduceUTable");
DeclareGlobalName("DeterminantGramUTable");

# Info class
DeclareInfoClass("InfoUTable");
# during development
SetInfoLevel(InfoUTable, 4);
