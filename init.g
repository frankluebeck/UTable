##  (C) 2025 Frank Lübeck (Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen)
##  
##  Read declaration files of the 'UTable' package
##  
ReadPackage( "UTable", "lib/UTable.gd");
ReadPackage( "UTable", "lib/PositionConjugacyClass.gd");
ReadPackage( "UTable", "lib/PowerMaps.gd");
ReadPackage( "UTable", "lib/SomeCharacters.gd");
ReadPackage( "UTable", "lib/Elementary.gd");
ReadPackage( "UTable", "lib/ScalarProducts.gd");
ReadPackage( "UTable", "lib/LLL.gd");
ReadPackage( "UTable", "lib/SplitByCentre.gd");

if (not IsBound(UTScalarProductInternal)) and
        IsKernelExtensionAvailable("UTable","scalar") then
  LoadKernelExtension("UTable", "scalar");
fi;

if (not IsBound(ReduceLLLRecordInternal)) and
        IsKernelExtensionAvailable("UTable","lll") then
  LoadKernelExtension("UTable", "lll");
elif not IsBound(ReduceLLLRecordInternal) then
  ReduceLLLRecordInternal := fail;
fi;
