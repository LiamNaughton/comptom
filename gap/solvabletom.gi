
#############################################################################
# assert A is abelian
OneMaximalNormalSubgroupAbelian:= function(A)
    local   gen;
    gen:= ShallowCopy(IndependentGeneratorsOfAbelianGroup(A));
    gen[1]:= gen[1]^Factors(Order(gen[1]))[1];
    return Subgroup(A, gen);
end;

#############################################################################
# assert G is solvable
OneMaximalNormalSubgroupSolvable:= function(G)
    local   hom,  max;
    hom:= NaturalHomomorphismByNormalSubgroupNC(G, DerivedSubgroup(G));
    max:= OneMaximalNormalSubgroupAbelian(ImagesSource(hom));
    return PreImage(hom, max);
end;


#############################################################################
# assert G is solvable
#############################################################################
##
#F  AllSubgroupClassesSolvable( G )
##
InstallGlobalFunction(AllSubgroupClassesSolvable, function(G)
    local   m;
    
    # trivial case first.
    if Size(G) = 1 then
        return [G];
    fi;
    
    #  otherwise recurse.
    m:= OneMaximalNormalSubgroupSolvable(G);
    return SubExtensionsSubgroups(G, m, AllSubgroupClassesSolvable(m));
end);
#############################################################################
##
#F  TomSolvableTom( G, maxcoma )
##
InstallGlobalFunction(TomSolvableTom, function(G, maxComa)
    local   m;
    
    # trivial case first.
    if Size(G) = 1 then
        return TableOfMarks(G);
    fi;
    
    #  otherwise recurse.
    m:= MaximalNormalSubgroups(G)[1];
    return TomExtensionTom(G, m, TomSolvableTom(m, maxComa), maxComa);
end);
