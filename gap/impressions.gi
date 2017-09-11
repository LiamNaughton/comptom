InfoTomExt:=NewInfoClass("InfoTomExt");

#############################################################################
PossibleTs:=function(A, K, p)
    local   cc;
    
    cc:= List(ConjugacyClasses(K), Representative);
    return Filtered(cc, x-> not x in A and Set(Factors(Order(x))) = [p]);
end;

#############################################################################
##
##  the set X(K, t), assuming t \in K \ A
##
XKt:=function(S, A, K, t)
    local   onClasses,  list,  C,  N,  clas,  o,  a,  s;
    
    onClasses:= function(c, a)
        return ConjugacyClass(K, Representative(c)^a);
    end;
    
    list:= [];
    C:= Centralizer(S, t);
    C:= Group(SmallGeneratingSet(C));
    N:= Normalizer(S, K);
    clas:= ConjugacyClasses(K);
    clas:= Filtered(clas, c-> IsConjugate(S, Representative(c), t));
    for o in Orbits(N, clas, onClasses) do
        Info(InfoTomExt,1,"#", Length(o)," \c");
        a:= Representative(o[1]);
        s:= RepresentativeAction(S, a, t);
        Append(list, Orbit(C, K^s));
    od;
    Info(InfoTomExt,1,["{", Length(list),"} \c"]);
    return list;
end;              


# extract one row from tom
ImpressionTom:= function(tom, i)
    local   subs,  marks,  imp;
    
    subs:= SubsTom(tom);
    marks:= MarksTom(tom);
    imp:= 0*[1..Length(marks)];
    imp{subs[i]}:= marks[i];
    return imp;
end;


# convert list into pos/val record
CompressedImp:= function(imp)
    local   pos,  val,  i;
    
    pos:= [];
    val:= [];
    for i in [1..Length(imp)] do
        if imp[i] <> 0 then
            Add(pos, i);
            Add(val, imp[i]);
        fi;
    od;
    return rec(pos:= pos, val:= val);
end;

# uncompress pos/val record into list of length len
UncompressedImp:= function(com, len)
    local   imp;
    
    imp:= 0*[1..len];
    imp{com.pos}:= com.val;
    return imp;
end;


NrContainedMaps:= function(map)
    return Product(Filtered(map, IsList), Length, 1);
end;


# apply pnq congruences to (parametrized) imp.  works in place.
DressRestrictImp:=  function(pnq, subref, imp, maxComa)
    local   p,  applyCongruence,  k,  dress,  db,  dr,  j,  impR,  
            nrCM,  sumB,  minR,  sumR,  new,  size,  maps;
    
    p:= subref.p;
    
    # how to check and apply a congruence locally
    applyCongruence:= function(cong)
        local   size,  impC,  nrCM,  maps;
        
        size:= Sum(cong.len);
        impC:= imp{cong.pos};
        nrCM:= NrContainedMaps(impC);
        if nrCM > 1 and nrCM < maxComa then
            maps:= ContainedMaps(impC);
            maps:= Filtered(maps, map-> (map * cong.len) mod size = 0);
            if maps = []  then
                Error("Panic: maps must not be empty");
            fi;
            imp{cong.pos}:= Parametrized(maps);
        fi;
    end;
    
    # red congruences first.
    for k in Reversed(subref.red) do
        applyCongruence(pnq[k]);
    od;
    
    # blue congruences next.
    for k in Reversed(subref.blue) do
        
#        applyCongruence(pnq[k]);
        
        # check red orbits vs blue.
        dress:= pnq[k];
        db:= [];  dr:= [];
        for j in [1..Length(dress.pos)] do
            if dress.pos[j] in subref.blue then
                Add(db, j);
            else
                Add(dr, j);
            fi;
        od;
        
        # continue only if red part is present.
        if dr = [] then
            continue;
        fi;
        db:= rec(len:= dress.len{db}, pos:= dress.pos{db});
        dr:= rec(len:= dress.len{dr}, pos:= dress.pos{dr});
        
        impR:= imp{dr.pos};
        nrCM:= NrContainedMaps(impR);
        if nrCM = 1 then 
            continue;
        fi;
                
        #  blue contribution.
        sumB:= imp{db.pos} * db.len;
        
        #  compute MINIMUM red contribution
        minR:= [];
        for j in dr.pos do
            if IsList(imp[j]) then
                Add(minR, imp[j][1]);  # imp[j][1] is the minimum of imp[j]
            else
                Add(minR, imp[j]);
            fi;
        od;
        sumR:= minR * dr.len;    # red contributes at least sumR.
        
        #  then check each relevant position for MAXIMUM possible contrib
        for j in dr.pos do
            if IsList(imp[j]) then
                new:= (p-1) * sumB - (sumR - imp[j][1]);  # balance
                if imp[j][Length(imp[j])] > new then
                    IntersectSet(imp[j], [0..new]);
                    if Length(imp[j]) = 1 then
                        imp[j]:= imp[j][1];
                    fi;
                fi;
            fi;
        od;
        
        # extract red portion of imp and apply test if feasible.
        size:= p * Sum(db.len);
        impR:= imp{dr.pos};
        nrCM:= NrContainedMaps(impR);
        if nrCM > 1 and nrCM < maxComa then
            maps:= ContainedMaps(impR);
            maps:= Filtered(maps, function(map) 
                sumR:= map * dr.len;  # use old local variable sumR
                return sumR <= (p-1) * sumB and (sumR + sumB) mod size = 0;
            end);
            if maps = []  then
                Error("Panic: maps must not be empty");
            fi;
            imp{dr.pos}:= Parametrized(maps);
        fi;
    od;
end;


#  how to compute an impression of S from those of A, and the pnq's.
#  (Parametrized and ContainedMaps are inverse GAP functions 
#  dealing with parametrized maps, ie. lists of numbers and lists.)
#
ImpressionExtensionBlue:= function(atom, subref, i)
    local   ref,  imp;
    
    # compute blue part 
    ref:= subref.ref[i];
    imp:= subref.p / Length(ref) * Sum(ref, j-> ImpressionTom(atom, j));
    imp:= imp{subref.ref{subref.blue}[1]};    #  redirect        
    imp{subref.red}:= 0 * subref.red;    # red part is zero (do we need this?)
            
    return imp;
end;


ImpressionExtensionRed:= function(atom, subref, pnq, i, maxComa)
    local   rangeBCC,  p,  imp,  k,  blk,  dress,  db,  dr,  j,  old,  
            minR,  balance,  x,  max,  ran,  l;
    
    # how to compute a range from a bounded congruence:
    # [a, b .. c] = { 0 <= x <= m : x mod d = l }
    rangeBCC:= function(m, d, l)
        return [l, l+d .. m - (m-l) mod d];
    end;
    
    p:= subref.p;
    
    # compute blue part
    imp:= ImpressionTom(atom, subref.ref[i]){subref.ref{subref.blue}[1]};
    imp{subref.red}:= 0 * subref.red;
    
    # diagonal entry.
    imp[i]:= Sum(pnq[i].len);
    
    ## then loop over k < subref.ref[i]
    # loop over blocks in reverse: there is one congruence per block!!!
    for k in Reversed([1..subref.ref[i]-1]) do
        blk:= subref.blk[k];
        
        if blk = [] then
            continue;
        fi;
                
        # find congruence that deals with this block and split
        dress:= pnq[subref.inv[k]];  # redirect!
        db:= [];  dr:= [];
        for j in [1..Length(dress.pos)] do
            if dress.pos[j] in subref.blue then
                Add(db, j);
            else
                Add(dr, j);
            fi;
        od;
        db:= rec(len:= dress.len{db}, pos:= dress.pos{db});
        dr:= rec(len:= dress.len{dr}, pos:= dress.pos{dr});
        
        # use blue entries as bounds
        old:= imp{subref.inv{subref.ref{blk}}}; # redirect!
        
        #  compute MINIMUM red contribution
        minR:= [];
        for j in dr.pos do
            if IsList(imp[j]) then
                Add(minR, imp[j][1]);  # imp[j][1] is the minimum of imp[j]
            else
                Add(minR, imp[j]);
            fi;
        od;
        balance:= (p-1) * (imp{db.pos} * db.len) - minR * dr.len;
        
        # loop over block
        for x in [1..Length(blk)] do
            
            # perm char values will be filled in later.
            if blk[x] in pnq[1].pos then
                continue;
            fi;
            
            # compute upper bound and initial range.
            max:= Minimum(balance, old[x]);
            if imp[i] mod p = 0 then
                ran:= rangeBCC(max, imp[i], 0);
            else
                l:= ChineseRem([imp[i], p], [0, old[x]]);
                ran:= rangeBCC(max, p * imp[i], l);
            fi;
            
            # singleton?
            if Length(ran) = 1 then
                ran:= ran[1];
            fi;
            
            imp[blk[x]]:= ran;
        od;
    od;            
    
    return imp;
end;

#############################################################################
##
##  compute exact numbers.
##
NrIncidents:= function(S, A, ccs, K, U)
    local   p,  ttk,  fusk,  ttu,  fusu,  l,  posk,  posu,  s,  xxx;
    
    p:= Index(S, A);
    
    ttk:= PossibleTs(A, K, p);
    fusk:= List(ttk, x-> PositionProperty(ccs, c-> x in c));

    ttu:= PossibleTs(A, U, p);
    fusu:= List(ttu, x-> PositionProperty(ccs, c-> x in c));
    
    # on the assumption that higher positions have smaller centralizers.
    l:= Maximum(fusu);
    posk:= Position(fusk, l);
    posu:= Position(fusu, l);
    
    s:= RepresentativeAction(S, ttu[posu], ttk[posk]);
    U:= U^s;
    
    xxx:= XKt(S, A, K, ttk[posk]);
    
    return Number(xxx, x-> IsSubgroup(x, U));
end;




# incidents counter: treat as many as possible.
FillIncidents:= function(S, A, imp, m, fil, ccs, K, kkk)
    local   p,  j,  U,  ttk,  fusk,  ttu,  fusu,  l,  posk,  posu,  s,  
            xxx,  val;
    
    p:= Index(S, A);
    
    j:=  fil[Length(fil)];
    U:= kkk[j];
    
    ttk:= PossibleTs(A, K, p);
    fusk:= List(ttk, x-> PositionProperty(ccs, c-> x in c));

    ttu:= PossibleTs(A, U, p);
    fusu:= List(ttu, x-> PositionProperty(ccs, c-> x in c));
    
    # on the assumption that higher positions have smaller centralizers.
    l:= Maximum(fusu);
    posk:= Position(fusk, l);
    posu:= Position(fusu, l);
    
    s:= RepresentativeAction(S, ttu[posu], ttk[posk]);
    U:= U^s;
    
    xxx:= XKt(S, A, K, ttk[posk]);
    
    val:= m * Number(xxx, x-> IsSubgroup(x, U));
    if val in imp[j] then
        imp[j]:= val;
        Info(InfoTomExt,1,[val, ", \c"]);
    else
        Error("Panic: val not in list");
    fi;
    
    # now look at the rest of the row
    for j in fil{[1..Length(fil)-1]} do
        U:= kkk[j];
        ttu:= PossibleTs(A, U, p);
        fusu:= List(ttu, x-> PositionProperty(ccs, c-> x in c));
        if l in fusu then
            posu:= Position(fusu, l);
            s:= RepresentativeAction(S, ttu[posu], ttk[posk]);
            U:= U^s;
            val:= m * Number(xxx, x-> IsSubgroup(x, U));
            if val in imp[j] then
                imp[j]:= val;
                Info(InfoTomExt,1,[val, ", \c"]);
            else
                Error("Panic: val not in list");
            fi;
        fi;
    od;
    
end;

    


#############################################################################
##
##  how to make it.
##
MakeIt:= function(ini, maxComa)
    local   S,  A,  atom,  sr,  pnq,  qnp,  i,  j,  k,  ccs,  fus,  c,  
            sub,  value,  pcSz,  szPc,  insertPermChar,  insertQnp,  
            minValue,  maxValue,  closeTransitively,  
            applyRestrictions,  finishOff,  marks, myrec, tom, st, mt, id, ug, norms, derived, tomrecord, substom,
	    markstom, identifier;
    
    S:= ini.S;
    A:= ini.A;
    atom:= ini.atom;
    sr:= ini.subref;
    pnq:= ini.pnq;
    
    # transpose pnq.
    qnp:= List(pnq, x-> rec(pos:= [], len:= [], ord:= []));
    for i in [1..Length(pnq)] do
        for j in [1..Length(pnq[i].pos)] do
            k:= pnq[i].pos[j];
            Add(qnp[k].pos, i);
            Add(qnp[k].len, pnq[i].len[j]);
            Add(qnp[k].ord, pnq[i].ord[j]);
        od;
    od;
    
    # determine fusion of red element classes to subgroups of S.
    SetConjugacyClassesSubgroups(S, List(sr.sub, x-> ConjugacyClassSubgroups(S, x)));
    ccs:= Filtered(ConjugacyClasses(S), c-> not Representative(c) in A);
    fus:= [];
    for c in ccs do
        sub:= Subgroup(S, [Representative(c)]);
        Add(fus, PositionProperty(ConjugacyClassesSubgroups(S), x-> sub in x));
    od;
    
    
    # how to read a value from a compressed (and unambiguous!) imp
    value:= function(a, b)
        local   p;
        p:= Position(marks[a].pos, b);
        if p = fail then
            return 0;
        fi;
        return marks[a].val[p];
    end;
    
    
    # how to compute perm char from class sizes.
    pcSz:= function(index, sz)
        return List([1..Length(ccs)], k-> sz[k] * index / Size(ccs[k]));
    end;
    
    
    # how to compute class sizes from perm char.
    szPc:= function(index, pc)
        return List([1..Length(ccs)], k-> pc[k] * Size(ccs[k]) / index);
    end;
    
    
    # how to insert perm char values.
    insertPermChar:= function(i)
        local   K,  sz,  c,  r,  j,  imp;
        
        # get a class representative.
        K:= sr.sub[i];
        
        # remember nonzero element classes
        sr.ttt[i]:= [];
        
        # compute perm char (or rather class intersection sizes)
        sz:= List(ccs, x-> 0);
        for c in ConjugacyClasses(K) do
            r:= Representative(c);
            if not r in A then
                j:= PositionProperty(ccs, x-> r in x);
                sz[j]:= sz[j] + Size(c);
                AddSet(sr.ttt[i], fus[j]);
            fi;
        od;
        
        # insert pc into impression
        imp:= marks[i];
        imp{fus}:= pcSz(Index(S, K), sz);
        
        # now improve bounds on marks
        for j in [sr.red[1]..i-1] do
            if IsList(imp[j]) then
                r:= Minimum(imp{sr.ttt[j]});
                if r < imp[j][Length(imp[j])] then
                    imp[j]:= Filtered(imp[j], x-> x <= r);
#                    Info(InfoTomExt,1,"!\c");
                    if Length(imp[j]) = 1 then
                        imp[j]:= imp[j][1];
#                        Info(InfoTomExt,1,"1\c");
                    fi;
                fi;
            fi;
        od;
        
        #  now check against earlier permchars.
        for j in [sr.red[1]..i-1] do
            if IsList(imp[j]) and 0 in imp[j] then
                if Minimum(sz - szPc(value(j, 1), List(fus, k-> value(j, k)))) < 0 then
                    imp[j]:= 0;
#                    Info(InfoTomExt,1,"?\c");
                fi;
            fi;
        od;
        
    end;
    
    
    # how to insert qnp.
    insertQnp:= function(i)
        local   q,  imp,  k,  j,  val;
        
        q:= qnp[i];
        imp:= marks[i];
        for k in [1..Length(q.len)] do
            j:= q.pos[k];
            val:= q.len[k] / Phi(q.ord[k]) * imp[i];
            if IsPrime(q.ord[k]) then
                if IsList(imp[j]) then
                    if val in imp[j] then
                        imp[j]:= val;
                        Info(InfoTomExt,1,",\c");
                    else
                        Error("Panic: val is not in list");
                    fi;
                else
                    if val <> imp[j] then
                        Error("Panic: val is different from value in imp");
                    fi;
                fi;
            else    # otherwise val is just a lower bound.
                if IsList(imp[j]) then
                    val:= Filtered(imp[j], x-> x >= val);
                    if val = [] then
                        Error("Panic: val is larger than values in imp");
                    else
                        if val <> imp[j] then
                            if Length(val) = 1 then
                                val:= val[1];
                            fi;
                            imp[j]:= val;
                            Info(InfoTomExt,1,"^\c");
                        fi;
                    fi;
                else
                    if val > imp[j] then
                        Error("Panic: val is larger than value in imp");
                    fi;
                fi;
            fi;
        od;
    end;
    
    
    # how to find the minimum value
    minValue:= function(a, b)
        if IsList(marks[a][b]) then
            return marks[a][b][1];
        else
            return marks[a][b];
        fi;
    end;
        
    
    # how to find the maximum value
    maxValue:= function(a, b)
        if IsList(marks[a][b]) then
            return marks[a][b][Length(marks[a][b])];
        else
            return marks[a][b];
        fi;
    end;
        
    
    # how to close under transitivity.
    closeTransitively:= function(i)
        local   imp,  k,  j,  max,  min;
        
        imp:= marks[i];
        for k in [sr.red[1]..i-1] do   #FIXME:  range!
            if IsList(imp[k]) then
                
                # use subgroups of k as upper bounds
                for j in marks[k].pos do
                    max:= maxValue(i, j);
                    if max < imp[k][Length(imp[k])] then
                        Info(InfoTomExt,1,"m\c");
                        SubtractSet(imp[k], [max+1..imp[k][Length(imp[k])]]);
                        if Length(imp[k]) = 1 then
                            imp[k]:= imp[k][1];
                        fi;
                        break;
                    fi;
                od;
            fi;
            
            if IsList(imp[k]) then
                
                #  find j between i and k that links i > j > k
                for j in [k+1..i-1] do
                    min:= minValue(i, j);
                    
                    # FIXME:  value(j, k) > 0 == k in marks[j].pos
                    if min > imp[k][1] and value(j, k) > 0 then 
                        Info(InfoTomExt,1,"=\c");
                        SubtractSet(imp[k], [0..min-1]);
                        if Length(imp[k]) = 1 then
                            imp[k]:= imp[k][1];
                        fi;
                        break;
                    fi;
                od;
            fi;
        od;
    end;


    # how to apply further restrictions.
    applyRestrictions:= function(i, maxComa)
        local   imp,  new,  old;
        
        imp:= marks[i];
        new:= Sum(Filtered(imp, IsList), Length);
        if new > 0 then
            repeat
                old:= new;
                closeTransitively(i);
                DressRestrictImp(pnq, sr, imp, maxComa);
                Info(InfoTomExt,1,"*\c");
                new:= Sum(Filtered(imp, IsList), Length);
            until new = old;
            Info(InfoTomExt,1,[" [", Number(imp, IsList), "] \c"]);
        fi;
    end;


    # how to compute values explicitly, as a last resort.
    finishOff:= function(i, maxComa)
        local   imp,  m,  fil;
        
        imp:= marks[i];
        m:= imp[i];
        
        while true do
            applyRestrictions(i, 10*maxComa);
            fil:= Filtered([1..Length(imp)], j-> IsList(imp[j]));
            if fil = [] then 
                return;
            fi;
            
            # starting with the rightmost,
            #        compute all values that can be sorted with the same t
            FillIncidents(S, A, imp, m, fil, ccs, sr.sub[i], sr.sub);
        od;
        Info(InfoTomExt,1,"\n");
    end;


    # initialize table of marks.
    marks:= [];
    
    # blue part.
    for i in sr.blue do
        marks[i]:= CompressedImp(ImpressionExtensionBlue(atom, sr, i));
    od;
    
    # a place to store hit element classes.
    sr.ttt:= [];
    
    # red part
    for i in sr.red do
        Info(InfoTomExt,1,["\n", i, " \c"]);
        marks[i]:= ImpressionExtensionRed(atom, sr, pnq, i, maxComa);
        Info(InfoTomExt, 1, [" [", Number(marks[i], IsList), "] \c"]);
        insertPermChar(i);
        insertQnp(i);
        applyRestrictions(i, maxComa);
        if not IsVector(marks[i]) then
            finishOff(i, maxComa);
        fi;
        marks[i]:= CompressedImp(marks[i]);
    od;
###########
#Changes
###########


    myrec:=rec( marks:= marks, sub:=GeneratorsListTom(S, ConjugacyClassesSubgroups(S)) );


    substom:=function(record)## Computes the list SubsTom

	local output, i;

	    output:=[];
	    for i in [1..Size(record.marks)] do
		Add(output, record.marks[i].pos);
	    od;
	return output;
    end;


    markstom:=function(record)##Computes the list MarksTom

	local output, i;

	output:=[];
	for i in [1..Size(record.marks)] do
	    Add(output, record.marks[i].val);
	od;
	return output;
   end;

##subs:=ini.subref.sub;


    identifier:=function(record)
    return StructureDescription(record.S);

    end;


    st:=substom(myrec);
    mt:=markstom(myrec);
    id:=identifier(ini);
    ug:=Group(GeneratorsOfGroup(ini.S));


    tom:=rec(Identifier:=id, SubsTom:= st, MarksTom:=mt,  UnderlyingGroup:=ug, GeneratorsSubgroupsTom:=myrec.sub);
    ##Make a table of marks object
    ConvertToTableOfMarks(tom);

    ##Compute NormalizersTom
    norms:=[];
    for i in [1..Size(st)] do
	Add(norms, NormalizerTom(tom, i));
    od;
    ##Update the tom record and make new table of marks object
    tom:=rec(Identifier:=id, SubsTom:= st, MarksTom:=mt,NormalizersTom:=norms,  UnderlyingGroup:=ug, GeneratorsSubgroupsTom:=myrec.sub);
    ConvertToTableOfMarks(tom);

    ##Compute DerivedSubgroupsTomUnique
    derived:=DerivedSubgroupsTom(tom);
    ##make new tom record
    tom:=rec(Identifier:=id, SubsTom:= st, MarksTom:=mt,NormalizersTom:=norms, DerivedSubgroupsTomUnique:=derived, UnderlyingGroup:=ug, GeneratorsSubgroupsTom:=myrec.sub);
    ## Keep a copy of the record
    tomrecord:=rec(Identifier:=id, SubsTom:= st, MarksTom:=mt,NormalizersTom:=norms, DerivedSubgroupsTomUnique:=derived, UnderlyingGroup:=ug, GeneratorsSubgroupsTom:=myrec.sub);
    ##Make table of marks object for the last time
    ConvertToTableOfMarks(tom);

    ##Return the record and the table of marks object
    ##return [tom,tomrecord] ;
    return tom;
    ## Old ending!!return rec(marks:= marks, sub:= sr.sub);
    ##return rec( marks:= marks, sub:=GeneratorsListTom(S, ConjugacyClassesSubgroups(S)) );
end;

InstallGlobalFunction(TomExtensionTom, function(S,A,tom, maxComa)

local l, hhh, kkk, ini, subref, pnq;
l:=Length(SubsTom(tom));
hhh:= List([1..l], i-> RepresentativeTom(tom, i));
subref:= SubGroupsAndRefs(S, A, hhh);

kkk:= subref.sub;
SetConjugacyClassesSubgroups(S, List(kkk, x-> ConjugacyClassSubgroups(S, x)));
pnq:=List([1..Length(kkk)], i -> PositionsNormalizerQuotient(S, i));
            
ini:= rec(S:= S, A:= A, atom:= tom, subref:= subref, pnq:= pnq);

return MakeIt(ini, maxComa);

end);
