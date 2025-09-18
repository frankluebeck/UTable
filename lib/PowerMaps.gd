###########################################################################
##  PowerMaps.gd
##  
##  (C) 2025 Frank Lübeck, Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen
##  
##  These files contains functions to find all power maps of the conjugacy
##  classes of a finite group.
##  

DeclareAttribute("PowerMapsOfAllClasses", IsGroup);

DeclareAttribute("RationalClassSets", IsGroup);

DeclareAttribute("MaximalCyclics", IsGroup);

DeclareGlobalName("InduceAllFromCyclicSubgroup");
DeclareGlobalName("InducedFromAllMaximalCyclicSubgroups");

DeclareGlobalName("PowerMapCharacters");
DeclareGlobalName("SmallPowerMapCharacters");

DeclareGlobalName("ActionAutomorphismsOnConjugacyClasses");
DeclareGlobalName("ActionAutomorphismsOnRationalClasses");
