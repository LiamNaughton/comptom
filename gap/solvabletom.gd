
#############################################################################
##
#F  AllSubgroupClassesSolvable( G )
##
##  <#GAPDoc Label="AllSubgroupClassesSolvable">
##  <ManSection>
##  <Func Name="AllSubgroupClassesSolvable" Arg='G'/>
##  <Description>
##  Given a solvable group <A>G</A>, <C>AllSubgroupClassesSolvable</C> computes a list of representatives of 
##  the conjugacy clases of subgroups of <A>G</A>, by first computing a composition series, and then applying 
##  <C>SubExtensionsSubgroups</C> repeatedly.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
  
DeclareGlobalFunction("AllSubgroupClassesSolvable");
#############################################################################
##
#F  TomSolvableTom( G , maxcoma)
##
##  <#GAPDoc Label="TomSolvableTom">
##  <ManSection>
##  <Func Name="TomSolvableTom" Arg='G, maxcoma'/>
##  <Description>
##  Given a solvable group <A>G</A> this function comptes the table of marks of <A>G</A> in an iterative fashion
##  by first computing a composition series and then applying <C>TomExtensionTom</C> repeatedly.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
  
DeclareGlobalFunction("TomSolvableTom");