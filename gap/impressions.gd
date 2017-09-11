#############################################################################
##
#F  TomExtensionTom( S, A, <tom>, maxcoma)
##
##  <#GAPDoc Label="TomExtensionTom">
##  <ManSection>
##  <Func Name="TomExtensionTom" Arg='S, A,tom,  maxcoma'/>
##  
##  <Description>
##  <C>TomExtensionTom</C> computes the table of marks of <A>S</A> from the table of marks of <A>A</A>. <A>A</A> must be normal in <A>S</A> of 
##  prime index. The third argument <A>tom</A> is the table of marks of <A>A</A>, while the additional argument <A>maxcoma</A>, is a bound on the number of 
##  contained maps,.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
  

DeclareGlobalFunction("TomExtensionTom");

