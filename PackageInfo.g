#############################################################################
##  
##  PackageInfo.g for the GAP 4 package comptom                  Liam Naughton
##  
SetPackageInfo( rec(
PackageName :=
  "comptom",
MyVersion :=
  "1r1p0",
MyWWWHome :=
  "http://www.scit.wlv.ac.uk/~in5296",
Subtitle :=
  "The GAP package comptom",
Version :=
  JoinStringsWithSeparator( SplitString( ~.MyVersion, "rp" ), "." ),
Autoload :=
  true,
Date :=
"25/08/2017",
PackageWWWHome :=~.MyWWWHome,
ArchiveURL :=
  Concatenation( ~.PackageWWWHome, "/", LowercaseString( ~.PackageName ),
                 ~.MyVersion ),
ArchiveFormats :=
  ".tar.gz,.zoo",
Persons := [
rec(
    LastName := "Naughton",
    FirstNames := "Liam",
    IsAuthor := true,
    IsMaintainer := true,
    Email := "liamjamesnaughton@gmail.com",
    WWWHome := ~.MyWWWHome,
    Place := "Wolverhampton",
    Institution := "School of Mathematics & Computer Science, University of Wolverhampton",
    PostalAddress := Concatenation( [
      "Liam Naughton\n",
      "School of Mathematics & Computer Science\n",
      "University of Wolverhampton\n",
      "Wulfruna Street\n",
      "Wolverhampton\n",
      "United Kingdom"
      ] )
  ),
  rec(
    LastName := "Pfeiffer",
    FirstNames := "G&ouml;tz",
    IsAuthor := true,
    IsMaintainer := true,
    Email := "goetz.pfeiffer@nuigalway.ie",
#   WWWHome := 
    Place := "Galway"
#   Institution := "",
#   PostalAddress := Concatenation( [
#     ] )
  ),
  ],
Status :=
  "deposited",
#CommunicatedBy :=
#  "name (place)",
#AcceptDate :=
#  "MM/YYYY",
README_URL :=
  Concatenation( ~.PackageWWWHome, "/README" ),
PackageInfoURL :=
  Concatenation( ~.PackageWWWHome, "/PackageInfo.g" ),
AbstractHTML := Concatenation( [
  "The package contains the <span class=\"pkgname\">GAP</span> ",
  "package comptom"
  ] ),
PackageDoc := rec(
  BookName :=
    "comptom",
  ArchiveURLSubset :=
    [ "doc", "htm" ],
  HTMLStart :=
    "htm/chapters.htm",
  PDFFile :=
    "doc/manual.pdf",
  SixFile :=
    "doc/manual.six",
  LongTitle :=
    "The GAP package comptom",
  Autoload :=
    true
  ),
Dependencies := rec(
  GAP :=
    ">= 4.4",
  NeededOtherPackages :=
    [["atlasrep", ">=1.4"]],
  SuggestedOtherPackages :=
    [ ["ctbllib", ">= 1.1"] ], # [["gpisotyp", ">= 1.0"]],
  ExternalConditions :=
    []
  ),
AvailabilityTest :=
  ReturnTrue,
TestFile :=
  "tst/testall.g",
Keywords :=
  [ "table of marks", "Burnside matrix", "subgroup lattice",
    "finite simple groups", "Moebius function", "Euler function" ],
) );

#############################################################################
##  
#E

