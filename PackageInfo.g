#############################################################################
##  
##  PackageInfo.g for the package 'UTable'
##                                                            
##  (C) 2025 Frank Lübeck (Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen)
##

SetPackageInfo( rec(

PackageName := "UTable",
Subtitle := "Constructing character tables with Unger's algorithm",
Version := "0.1",
Date := "22/08/2025", # dd/mm/yyyy format
License := "GPL-3.0-or-later",

Persons := [
  rec(
    IsAuthor := true,
    IsMaintainer := true,
    FirstNames := "Frank",
    LastName := "Lübeck",
    Email := "Frank.Luebeck@math.rwth-aachen.de",
    Place := "Aachen",
    Institution := "RWTH Aachen",
  ),
],

SourceRepository := rec(
    Type := "git",
    URL := "https://github.com/frankluebeck/UTable",
),
IssueTrackerURL := Concatenation( ~.SourceRepository.URL, "/issues" ),

PackageWWWHome :="https://TODO",

PackageInfoURL := Concatenation( ~.PackageWWWHome, "PackageInfo.g" ),
README_URL     := Concatenation( ~.PackageWWWHome, "README" ),
ArchiveURL     := Concatenation( ~.PackageWWWHome, "UTable-", ~.Version ),

ArchiveFormats := ".tar.gz",

Status := "experimental",

AbstractHTML   :=  "Interactive and non-interactive construction of \
the ordinary character table of a finite group, based on Unger's algorithm.",

PackageDoc := rec(
  BookName  := "UTable",
  ArchiveURLSubset := ["doc"],
  HTMLStart := "doc/chap0_mj.html",
  PDFFile   := "doc/manual.pdf",
  SixFile   := "doc/manual.six",
  LongTitle := "Constructing character tables using Unger's algorithm",
),

Dependencies := rec(
  GAP := ">= 4.14",
  NeededOtherPackages := [ [ "GAPDoc", ">= 1.5" ] ],
  SuggestedOtherPackages := [ ],
  ExternalConditions := [ ],
),

AvailabilityTest := ReturnTrue,

TestFile := "tst/testall.g",

Keywords := [ ],

) );
