#############################################################################
##
##  Given S > A > H such that A is normal of prime index in S
##  find (up to conjugation) all H < K < S such that K \cap A = H.
##

InfoSubs:=NewInfoClass("InfoSubs");

SubExtensions:= function(S, A, H)
    local   p,  nor,  hom,  quo,  list,  rats,  class,  y,  x,  m;
    
    p:= Index(S, A);
    nor:= Normalizer(S, H);
    
    # Check if H fuses
    if IsSubgroup(A, nor) then
        return 0;
    fi;
    
    hom:= NaturalHomomorphismByNormalSubgroupNC(nor, H);
    quo:= ImagesSource(hom);
    
    list:= [];  rats:= [];
    for class in ConjugacyClasses(quo) do
        y:= Representative(class);
        x:= PreImagesRepresentative(hom, y);
        if not x in A and x^p in H  then
            if p = 2 then  # don't need to use rational classes
                # make x a p-element
                m:= Product(Filtered(Factors(Order(x)), z-> z <> p));
                Add(list, x^m);
            else
                if not ForAny(rats, z-> y in z)  then  
                    Add(rats, RationalClass(quo, y));
            
                    # make x a p-element
                    m:= Product(Filtered(Factors(Order(x)), z-> z <> p));
                    Add(list, x^m);
                fi;
            fi;
        fi;
    od;
    
    return list;
end;

#############################################################################
##  
##  given a list hhh of subgroups representing conjugacy classes of A,
##  find out which classes fuse under S, and which classes of S correspond
##  to the ones that don't fuse.
##
##  returns a record with components:
##
##    p: the index of A in S (assert p is prime)
##    blue:
##    red:
##
BlueRedSubgroups:= function(S, A, hhh)
    local   p,  blue,  ccc,  bbb,  red,  i,  ext,  j;
    
    p:= Index(S, A);
    Info(InfoSubs, 1,Length(hhh), ".", p);
    blue:= [];  ccc:= [];  bbb:= [];
    red:= List(hhh, x-> []);
    for i in [1..Length(hhh)] do
        ext:= SubExtensions(S, A, hhh[i]);
        if ext = 0 then
            j:= PositionProperty(ccc, c-> hhh[i] in c);
            if j = fail then
                Add(blue, [i]);
                Add(ccc, ConjugacyClassSubgroups(S, hhh[i]));
                Add(bbb, Length(blue));
            else
                Add(blue[bbb[j]], i); 
                if Length(blue[bbb[j]]) = p then  # the class is full.
                    Remove(ccc, j);  Remove(bbb, j);
                fi;
            fi;
        else
            red[i]:= ext;
        fi;
	
    od;
    Info(InfoSubs, 1, Length(blue));
    return rec(p:= p, blue:= blue,  red:= red);
end;

#############################################################################
##
#F  SubExtensionsSubgroups( S, A, hhh)
##
InstallGlobalFunction(SubExtensionsSubgroups, function(S,  A,  hhh)
    local   br,  blue,  red,  i,  l;
    
    br:= BlueRedSubgroups(S, A, hhh);
    blue:= Difference(Union(br.blue), List(br.blue, x-> x[1]));
    blue:= hhh{Difference([1..Length(hhh)], blue)};
    red:= [];
    for i in [1..Length(hhh)] do
        for l in br.red[i] do
            Add(red, ClosureGroup(hhh[i], l));
        od;
    od;
    
    return Concatenation(blue, red);
end);


SubGroupsAndRefs:= function(S,  A,  hhh)
    local   br,  ref,  inv,  i,  j,  o,  blk,  blue,  red,  l,  sub;
    
    br:= BlueRedSubgroups(S, A, hhh);
    
    ref:= Difference([1..Length(hhh)], Union(br.blue));
    ref:= List(ref, x-> [x]);
    ref:= Union(ref, br.blue);
    inv:= [];
    for i in [1..Length(ref)] do
        for j in ref[i] do
            inv[j]:= i;
        od;
    od;
    
    o:= Length(ref);  #  offset: red groups start right after here.
    for i in [1..Length(br.red)] do
        Append(ref, List(br.red[i], x-> i));
    od;
    
    blk:= List(inv, x-> []);
    for i in [o+1 ..Length(ref)] do
        Add(blk[ref[i]], i);
    od;
        
    blue:= Difference(Union(br.blue), List(br.blue, x-> x[1]));
    blue:= hhh{Difference([1..Length(hhh)], blue)};
    red:= [];
    for i in [1..Length(hhh)] do
        for l in br.red[i] do
            Add(red, ClosureGroup(hhh[i], l));
        od;
    od;
    return rec(p:= br.p,
               sub:= Concatenation(blue, red),
               ref:= ref,
               inv:= inv,
               blk:= blk,
               blue:= [1..Length(blue)],
               red:= [Length(blue) + 1..Length(blue) + Length(red)]);
end;


#############################################################################
##
##  Given S, its classes of subgroups ccs, and an index i, 
##  find the positions in ccs of the conjugacy class of the 
##  normalizer quotient, and their lengths.
##
PositionsNormalizerQuotient:= function(S, i)
    local   ccs,  classOf,  H,  nor,  hom,  quo,  len,  pos,  ord,  
            class,  y,  x,  C,  ooo,  j;
    
    ccs:= ConjugacyClassesSubgroups(S);
    
    # how to find the class of c
    classOf:= function(c)
        local   sol,  j,  C,  r;
        
        sol:= SortedList(OrbitLengths(c));
        for j in [i..Length(ccs)] do
            C:= ccs[j];
            r:= Representative(C);
            if Size(c) = Size(r) and sol = SortedList(OrbitLengths(r)) and c in C then
                return j;
            fi;
        od;
    end;
    
    H:= Representative(ccs[i]);
    nor:= Normalizer(S, H);
    hom:= NaturalHomomorphismByNormalSubgroupNC(nor, H);
    quo:= ImagesSource(hom);
    
    len:= [];  pos:= [];  ord:= [];
    for class in ConjugacyClasses(quo) do
        Add(len, Size(class));
        y:= Representative(class);
        x:= PreImagesRepresentative(hom, y);
        C:= ClosureGroup(H, x);
        Add(pos, classOf(C));
        Add(ord, Order(y));
    od;
    
    # normalize and compress
    nor:= 0*[1..Maximum(pos)];
    ooo:= [];
    for j in [1..Length(pos)] do
        nor[pos[j]]:= nor[pos[j]] + len[j];
        ooo[pos[j]]:= ord[j];
    od;
    
    len:= [];  pos:= [];  ord:= [];
    for j in [1..Length(nor)] do
        if nor[j] <> 0 then
            Add(pos, j);
            Add(len, nor[j]);
            Add(ord, ooo[j]);
        fi;
    od;
        
    return rec(len:= len, pos:= pos, ord:= ord);
end;


#############################################################################
##
##  How to get initial data for a library tom of A_n
##
InitialData:= function(n)
    local   S,  A,  tom,  l,  hhh,  subref,  kkk,  pnq,  i;
    
    S:= SymmetricGroup(n);
    A:= AlternatingGroup(n);
    tom:= TableOfMarks(Concatenation("A", String(n)));
    
    l:=  Length(MarksTom(tom));
    hhh:= List([1..l], i-> RepresentativeTom(tom, i));
    SetConjugacyClassesSubgroups(A, List(hhh, x-> ConjugacyClassSubgroups(A, x)));
    subref:= SubGroupsAndRefs(S, A, hhh);
    kkk:= subref.sub;
    SetConjugacyClassesSubgroups(S, List(kkk, x-> ConjugacyClassSubgroups(S, x)));
    pnq:= [];
    for i in [1..Length(kkk)] do
        pnq[i]:= PositionsNormalizerQuotient(S, i);
        Info(InfoSubs,1,":\c");
        if i mod 1000 = 0 then
            Info(InfoSubs,1,i);
        fi;
    od;
     Info(InfoSubs,1,"\n");
            
    return rec(S:= S, A:= A, atom:= tom, subref:= subref, pnq:= pnq);
end;


