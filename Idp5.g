#############################################################################################
##
## GAP code for the paper 
##     Group Identification for the groups of order dividing p^5
##     arxiv: TBA
## by
##     Heiko Dietrich, Bettina Eick, Henrik Schanze
##
##
#######################
## Main functions:
#######################
##
## IdSmallGroup
##     method for groups of order dividing p^5, implemented via p5id_IdSmallGroup
##     takes a p-group of order dividing p^5 and returns IdSmallGroup
##
 
DeclareAttribute("IsomorphismSmallGroup",IsGroup);
## takes as input a group and, if implemented, constructs an iso G-->SmallGroup(IdSmallGroup(G))

## IsomorphismSmallGroup
##     method for groups of order dividing p^5, implemented via p5id_IsomorphismSmallGroup
##     N.B.: for G of order p^5 the algorithm is experimental and randomised, and 
##           it is possible that the random search fails. In this case 'fail' is returned
##     N.B.: the lifting for p^5 was coded with Claude Opus, Lines 1948-3633
##
## IdSmallGroupFromType_p5:
##     takes prime p>5 and type t in [1..70] (or a pair [t,k]), returns all ids i such that
##     the group with IDSmallGroup = [p^5,i] has "type" t (type [t,k]).
##
##
## TypeFromIdSmallGroup_p5:
##     takes a prime p>5 and i in [1..NumberSmallGroups(p^5)] and returns type of
##     SmallGroup(p^5,i)
##
## TestSmallGroupID_p5:
##     takes list lps of primes, integer nr, and Boolean testIso
##     runs over all p in lps and tests the ID for nr copies of SmallGroup(p^e,i) for
##     all e = 1,2,3,4,5 and i in [1..NumberSmallGroups(p^e)
##     if testAut = true, then also test isomorphism to standard copy
##     for e=5 also displays a runtime statistic at the end.
##
##     NB: some iso-tests may take time, so run these test separately maybe
##
#######################
## Info Levels:
##
DeclareInfoClass("myp5id");
SetInfoLevel(myp5id,1);
DeclareInfoClass("myp5id_time");
SetInfoLevel(myp5id_time,1);
##
##
## name space is "p5id_"
##



#######################################################################
## Returns id(s) of groups of order p^5 that that belong to type. If more than one
## group belongs to type, a list of ids is returned. If just one groups has type,
## the id itself is returned.
## input: prime p and type (either a single integer or a pair of integers)
## output: a single interger or a list of integers
##
IdSmallGroupFromType_p5:=function(p, type)
    local res, gettypes, ids;

    if not IsPrimeInt(p) or not p>5 or
       not ((IsInt(type) and type in [1..70]) or
            (IsList(type) and Length(type)=2 and type[1] in [1..70])) then
       Error("wrong input");
    fi;   

    gettypes := function(p,i)
        local f, c, w,a,b,type,k;
        w := IntFFE( Z( p ) );
        a := Gcd( p - 1, 3 );
        b := Gcd( p - 1, 4 );
        if i <= 10 then
            type := i;
        elif i <= 11 + (p - 1) / 2 - 1 then
            type := 11;
            k := i - 10;
        elif i <= 11 + p - 2 then
            type := 12;
            k := i - (11 + (p - 1) / 2 - 1);
        elif i <= 25 + p then
            type := i - p + 3;
        elif i <= 25 + p + a then
            type := 29;
            k := i - (25 + p);
        elif i <= 27 + p + a then
            type := i - p - a + 4;
        elif i <= 27 + p + 2 * a then
            type := 32;
            k := i - (27 + p + a);
        elif i <= 27 + p + 2 * a + b then
            type := 33;
            k := i - (27 + p + 2 * a);
        elif i <= 41 + p + 2 * a + b then
            type := i - p - 2 * a - b + 6;
        elif i <= 41 + p + 2 * a + b + (p - 1) / 2 then
            type := 48;
            k := i - (41 + p + 2 * a + b);
        elif i = 42 + p + 2 * a + b + (p - 1) / 2 then
            type := 49;
        elif i <= 42 + p + 2 * a + b + p - 1 then
            type := 50;
            k := i - (42 + p + 2 * a + b + (p - 1) / 2);
        else
            type := i - 2 * p - 2 * a - b + 9;
        fi;
        return type;
    end;

    if IsInt(type) then
        ids := Filtered([1..NumberSmallGroups(p^5)],i->gettypes(p,i)=type);
        if Size(ids) = 1 then ids := ids[1]; fi;
    elif IsList(type) then
        ids := Filtered([1..NumberSmallGroups(p^5)],i->gettypes(p,i)=type[1]);
        if Size(ids) < type[2] then Error("Type does not exist"); fi;
        ids := ids[type[2]];
    fi;

    return ids;
end;



#######################################################################
## the inverse of IdSmallGroupFromType_p5
## input: prime p>5 and i in [1..NumberSmallGroups(p^5)]
## output: the type of the group with IDSmallGroup=[p^5,i]
##
TypeFromIdSmallGroup_p5 := function(p,i)
local f, c, w,a,b,typ,k;

    if not IsPrimeInt(p) or not p>5 or not i in [1..NumberSmallGroups(p^5)] then
       Error("wrong input");
    fi;   
    f := FreeGroup( 5 );
    c := CombinatorialCollector( f, [ p, p, p, p, p ] );
    w := IntFFE( Z( p ) );
    a := Gcd( p - 1, 3 );
    b := Gcd( p - 1, 4 );
    k := false;

    if i <= 10 then
        typ := i;
    elif i <= 11 + (p - 1) / 2 - 1 then
        typ := 11;
        k := i - 10;
    elif i <= 11 + p - 2 then
        typ := 12;
        k := i - (11 + (p - 1) / 2 - 1);
    elif i <= 25 + p then
        typ := i - p + 3;
    elif i <= 25 + p + a then
        typ := 29;
        k := i - (25 + p);
    elif i <= 27 + p + a then
        typ := i - p - a + 4;
    elif i <= 27 + p + 2 * a then
        typ := 32;
        k := i - (27 + p + a);
    elif i <= 27 + p + 2 * a + b then
        typ := 33;
        k := i - (27 + p + 2 * a);
    elif i <= 41 + p + 2 * a + b then
        typ := i - p - 2 * a - b + 6;
    elif i <= 41 + p + 2 * a + b + (p - 1) / 2 then
        typ := 48;
        k := i - (41 + p + 2 * a + b);
    elif i = 42 + p + 2 * a + b + (p - 1) / 2 then
        typ := 49;
    elif i <= 42 + p + 2 * a + b + p - 1 then
        typ := 50;
        k := i - (42 + p + 2 * a + b + (p - 1) / 2);
    else
        typ := i - 2 * p - 2 * a - b + 9;
    fi;

    if IsInt(k) then
        return [typ, k];
    else
        return [typ];
    fi;
end;



#####################################################################################
#####################################################################################
#####################################################################################
#####################################################################################
#####################################################################################
#####################################################################################
##
##
## functions
##
##
#####################################################################################
#####################################################################################
#####################################################################################



#####################################################################################
## input:  a p-group G of size 1, p, p^2, p^3, or p^4, and optional Boolean argument
## "test"
## output: record with id and iso to SmallGroup(id); if test=true, then do not use NC
## functions
#
p5id_p4IsoStandard := function(arg)
    local n, p, e, Gstd, iso, g, h, k, l, U, sz, id, hom, gen, z, i, ord, max, m, new, done, gen_final, im_final, test, G, want, t, O,j, Ug, Upc, pcg, mat, l9, l10, i9, i10, R, kk, ll, hh, gg, hh2;


   if Length(arg)=2 then test := arg[2]; else test:=false; fi;
   G   := arg[1];
   sz  := Size(G);
   n   := Collected(FactorsInt(Size(G)));
   iso := 0;

   if not Length(n)=1 then Error("input needs to be p-group of order dividing p^4"); fi;

   #########################################################

    ## case n=[*,1]
    if Size(n)=1 and n[1][2] = 1 then
        Gstd := SmallGroup(n[1]);
        g := First(Concatenation(GeneratorsOfGroup(G),[One(G)]),x->Order(x)=sz);
        h := First(Concatenation(GeneratorsOfGroup(Gstd),[One(Gstd)]),x->Order(x)=sz);
        gen_final := [g];
        im_final  := [h];
        id        := n[1];

   #########################################################

    ## case n=p^2
    elif Size(n)=1 and n[1][2] = 2 then
        if IsCyclic(G) then
            Gstd := SmallGroup(sz,1);
            g   := First(Concatenation(GeneratorsOfGroup(G),[One(G)]),x->Order(x)=sz);
            h   := First(Concatenation(GeneratorsOfGroup(Gstd),[One(Gstd)]),x->Order(x)=sz);
            gen_final := [g];
            im_final  := [h];
            id  := [sz,1];
        else
            Gstd := SmallGroup(sz,2);
            g   := First(GeneratorsOfGroup(G), x-> not x=One(G));
            U   := Subgroup(G,[g]);
            h   := First(GeneratorsOfGroup(G),x-> not x in U);
            gen_final := [g,h];
            im_final  := [Gstd.1,Gstd.2];
            id  := [sz,2];
        fi;

   ##########################################################

   ## case n=p^3

   elif Size(n)=1 and n[1][2] = 3 then

      p := n[1][1];

      if IsAbelian(G) then

         if IsCyclic(G) then
           Gstd := SmallGroup(sz,1);
	   g   := First(GeneratorsOfGroup(G),x->Order(x)=sz);
           h   := First(GeneratorsOfGroup(Gstd),x->Order(x)=sz);
	   gen_final := [g];
           im_final  := [h];
           id  := [sz,1];

         elif ForAll(GeneratorsOfGroup(G),x->Order(x) in [1,p]) then
            Gstd := SmallGroup(sz,5);
	    h   := First(GeneratorsOfGroup(G),x-> Order(x)=p);
	    U   := Subgroup(G,[h]);
	    k   := First(GeneratorsOfGroup(G),x-> not x in U);
	    U   := Subgroup(G,[h,k]);
	    l   := First(GeneratorsOfGroup(G),x-> not x in U);
            gen_final := [h,k,l];
            im_final  := [Gstd.1,Gstd.2,Gstd.3];
	    id  := [sz,5];

         else #p^2 x p

            Gstd := SmallGroup(sz,2);
            h   := First(GeneratorsOfGroup(G),x-> Order(x)=p^2);
	    U   := Subgroup(G,[h]);
	    k   := First(GeneratorsOfGroup(G),x-> not x in U);
	    if not Order(k)=p then i := First([1..p-1],x-> Order(h^x*k)=p); k:=h^i*k; fi;
	    gen_final := [h,k];
            im_final  := [Gstd.1,Gstd.2];
	    id  := [sz,2];

         fi;

      else ## nonabelian

         if sz = 8 then

            id  := IdSmallGroup(G);
	    iso := IsomorphismGroups(G,SmallGroup(id));
	    return rec(id:=id, iso:=iso);

         else ## odd p

	    z   := Centre(G);
	    hom := NaturalHomomorphismByNormalSubgroup(G,z);
	    gen := List(MinimalGeneratingSet(Image(hom)),x->PreImagesRepresentative(hom,x));

            if Exponent(G)=p then

               Gstd := SmallGroup(sz,3);
	       id   := [sz,3];
	       gen_final := Concatenation(gen, [Comm( gen[2], gen[1] )] );
	       im_final  := [Gstd.1,Gstd.2, Gstd.3];

            else ## exponent p^2 .... this case is still a bit brute force

               Gstd := SmallGroup(sz,4);
	       id   := [sz,4];
	       ord  := List(gen,Order);
	       if not ord[1]=p^2 then gen := gen{[2,1]}; ord := ord{[2,1]}; fi;
	       g    := gen[1];
	       z    := g^p;
	       want := gen[2]^p;
	       if ord[1]=p^2 and ord[2]=p^2 then
	          i := First([1..p-1],x-> want=z^x);
		 #i := First([1..p^2-1],x-> Order(gen[1]^x*gen[2])=p);
		  gen[2] := gen[1]^-i*gen[2];
               fi;
	       h    := gen[2];
	       i    := First([1..p-1],x-> Comm(h^x,g)=z);
	       gen_final := [g,h^i,z];
	       im_final  := [Gstd.1,Gstd.2, Gstd.3];
            fi;
         fi;
      fi;


   #############################################

   ### p^4
   elif Size(n)=1 and n[1][2] = 4 then
      p := n[1][1];

      ## case p=2 and p=3 bruteforce
      if p in [2,3] then
         id   := IdSmallGroup(G);
	 iso  := IsomorphismGroups(G,SmallGroup(id));
	 Gstd := SmallGroup(id);
	 return rec(id:=id, iso:=iso);


      else ## odd case

         if IsAbelian(G) then
	    gen := List(MinimalGeneratingSet(G),x->x);
	    ord := List(gen,Order);
	    SortParallel(ord,gen);
	    ord       := Reversed(ord);
	    gen_final := Reversed(gen);
	    if ord=[p^4] then
	       id     := [sz,1];
	       Gstd     := SmallGroup(sz,1);
	       im_final :=MinimalGeneratingSet(Gstd);
	    elif ord=[p,p,p,p] then
               Gstd     := SmallGroup(sz,15);
	       im_final := GeneratorsOfGroup(Gstd);
	       id       := [sz,15];
            elif ord = [p^3,p] then
               Gstd     := SmallGroup(sz,5);
	       im_final := [Gstd.1,Gstd.2];
	       id       := [sz,5];
            elif ord = [p^2,p^2] then
               Gstd := SmallGroup(sz,2);
	       im_final := [Gstd.1,Gstd.2];
	       id       := [sz,2];
	    elif ord = [p^2,p,p] then
               Gstd     := SmallGroup(sz,11);
	       im_final := [Gstd.1,Gstd.2,Gstd.3];
	       id       := [sz,11];
            fi;


         else ###############################################  nonabelian case

            if Exponent(G) = p^3 then ## C_{p^3} : C_p

               id   := [sz, 6];
               Gstd := SmallGroup(id);
	       g    := First(GeneratorsOfGroup(G),x->Order(x)=p^3); ## does exist
	       z   := g^(p^2);
               U   := Subgroup(G,[g]);
	       repeat h := Random(G); until not h in U;
	       if Order(h)=p^3 then
                  want := h^(p^2);
		  i    := First([1..p-1],x-> want = z^x);
		  h    := g^-i * h;
	       fi;
	       if Order(h)=p^2 then
	          want := h^p;
		  i    := First([1..p-1],x-> want = z^x);
		  h    := g^(-i*p)*h;
	       fi;
	       i         := First([1..p-1],x-> Comm(h^x,g)=z);
               gen_final := [g,h^i];
	       im_final  := [Gstd.1,Gstd.2];


            elif Exponent(G) = p and Size(Centre(G)) = p^2 then # Cp \ltimes C_p^3


               id   := [sz, 12];
	       Gstd := SmallGroup(id);
               z    := Centre(G);
	       hom := NaturalHomomorphismByNormalSubgroup(G,z);
	       gen := List(MinimalGeneratingSet(Image(hom)),x->PreImagesRepresentative(hom,x));
               g   := gen[1];
	       h   := gen[2];
	       l   := Comm(h,g);
	       U   := Subgroup(G,[l]);
	       k   := First([z.1,z.2], x-> not x in U);
	       gen_final := [g,h,k,l];
	       im_final  := [Gstd.1,Gstd.2,Gstd.3,Gstd.4];


            elif Exponent(G)= p and Size(Centre(G)) = p then  # Cp \ltimes C_p^3

               id   := [sz, 7];
	       Gstd := SmallGroup(id);
	       U    := Centraliser(G,FrattiniSubgroup(G)); #p x p x p
	       ## the following is faster than MinimalGeneratingSet(U) for p=101
	       Ug   := [];
	       for z in GeneratorsOfGroup(U) do
	          if not z in SubgroupNC(G,Ug) then Add(Ug,z); fi;
		  if Size(Ug)=3 then break; fi;
	       od;
	       l    := MinimalGeneratingSet(Centre(G))[1];
	       if not    l in Subgroup(U,Ug{[1,2]}) then t:=[Ug[1],Ug[2],l];
	       elif not  l in Subgroup(U,Ug{[2,3]}) then t:=[Ug[2],Ug[3],l];
	       elif not  l in Subgroup(U,Ug{[1,3]}) then t:=[Ug[1],Ug[3],l]; fi;
               Upc  := AbelianGroup([p,p,p]);
	       g    := First(GeneratorsOfGroup(G),x-> not x in U);
	       iso  := GroupHomomorphismByImagesNC(U,Upc,t,MinimalGeneratingSet(Upc));
	       pcg  := PcgsByPcSequence(FamilyObj(One(Upc)),List(t,x->Image(iso,x)));
	       mat  := List(t,x-> ExponentsOfPcElement(pcg,Image(iso,x^g)))*One(GF(p));
               k    := SolutionMat(mat-mat^0,[0,0,1]*One(GF(p)));
	       h    := SolutionMat(mat-mat^0,k);
	       k    := PreImagesRepresentative(iso,PcElementByExponents(pcg,List(k,Int)));
	       h    := PreImagesRepresentative(iso,PcElementByExponents(pcg,List(h,Int)));
	       gen_final := [g,h,k,l];
	       im_final  := [Gstd.1,Gstd.2,Gstd.3,Gstd.4];


            elif Exponent(G)=p^2 and Size(Centre(G))=p^2 and IsCyclic(Centre(G)) then
	       id := [sz,14];
               Gstd := SmallGroup(id);
               z    := Centre(G);
	       hom := NaturalHomomorphismByNormalSubgroup(G,z);
	       gen := List(MinimalGeneratingSet(Image(hom)),x->PreImagesRepresentative(hom,x));
               z   := Centre(G);
	       g   := gen[1];
	       h   := gen[2];
	       l   := Comm(h,g);
               z   := First(GeneratorsOfGroup(z),x->Order(x)=p^2);
	       i   := First([1..p-1],x-> z^(x*p) = l);
	       z   := z^i;
	       if Order(g)=p^2 then
   	          i   := First([0..p-1],x-> g^p = z^(x*p));
   	          g   := g*z^-i;
	       fi;
	       if Order(h)=p^2 then
	          i   := First([0..p-1],x-> h^p = z^(x*p));
	          h   := h*z^-i;
	       fi;
               gen_final := [g,h,z,l];
	       im_final  := [Gstd.1,Gstd.2,Gstd.3,Gstd.4];


            elif Exponent(G)=p^2 and RankPGroup(G)=3 then

               id   := [sz,13];
               Gstd := SmallGroup(id);
               z    := Centre(G);
	       hom  := NaturalHomomorphismByNormalSubgroup(G,z);
	       gen  := List(MinimalGeneratingSet(Image(hom)),x->PreImagesRepresentative(hom,x));
               z   := FrattiniSubgroup(G);
	       g   := gen[1];
	       h   := gen[2];
	       if not Order(g)=p^2 then t := g; g := h; h := t; fi;
	       l   := g^p;
	       if Order(h)=p^2 then
                  i   := First([0..p-1],x-> h^p = l^(x));
	          h   := h*g^-i;
               fi;
	       i   := First([1..p-1],x-> Comm(h^x,g)=l);
	       h   := h^i;
	       z   := First(GeneratorsOfGroup(Centre(G)),x-> not x in FrattiniSubgroup(G));
               gen_final := [g,h,z,l];
	       im_final  := [Gstd.1,Gstd.2,Gstd.3,Gstd.4];

	    elif Size(Centre(G))=p^2 and Size(Omega(G,p))=p^3 then
               id   := [sz,3];
               Gstd := SmallGroup(id);
	       O    := Omega(G,p);
	       g    := First(GeneratorsOfGroup(G),x->Order(x)=p^2);
	       l    := g^p;
	       U    := Subgroup(O,[l]);
	       h    := First(GeneratorsOfGroup(O),x-> not Comm(x,g) in U);
	       k    := Comm(h,g);
               gen_final := [g,h,k,l];
	       im_final  := [Gstd.1,Gstd.2,Gstd.3,Gstd.4];


            elif Size(Centre(G))=p^2 and Size(Omega(G,p))=p^2 then
               id   := [sz,4];
               Gstd := SmallGroup(id);
               z    := Centre(G);
	       hom  := NaturalHomomorphismByNormalSubgroup(G,z);
	       gen  := List(MinimalGeneratingSet(Image(hom)),x->PreImagesRepresentative(hom,x));
	       g    := gen[1];
	       h    := gen[2];
	       U    := DerivedSubgroup(G);
	       if g^p in U and not h^p in U then
	          t := h; h:=g; g:=t;
	       elif not g^p in U and not h^p in U then
  	          i    := First([0..p-1],x-> (g^x*h)^p in U);
	          h    := g^i*h;
	       fi; #now h^p generates G'
	       k    := h^p;
	       j    := First([1..p-1],x-> Comm(h,g^x)=k);
	       g    := g^j;
	       l    := g^p;
	       gen_final := [g,h,k,l];
	       im_final  := [Gstd.1,Gstd.2,Gstd.3,Gstd.4];


            elif Exponent(Centraliser(G,FrattiniSubgroup(G)))=p then

	       id    := [sz,8];
               Gstd := SmallGroup(id);
	       U    := Centraliser(G,FrattiniSubgroup(G)); #this is Omega(G,p), but the latter hard to construct!
	       ## the following is faster than MinimalGeneratingSet(U) for p=101
	       Ug   := [];
	       for z in GeneratorsOfGroup(U) do
	          if not z in SubgroupNC(G,Ug) then Add(Ug,z); fi;
		  if Size(Ug)=3 then break; fi;
	       od;
	       Upc  := AbelianGroup([p,p,p]);
	       g    := First(GeneratorsOfGroup(G),x-> not x in U);
	       l    := g^p;
	       if not    l in Subgroup(U,Ug{[1,2]}) then t:=[Ug[1],Ug[2],l];
	       elif not  l in Subgroup(U,Ug{[2,3]}) then t:=[Ug[2],Ug[3],l];
	       elif not  l in Subgroup(U,Ug{[1,3]}) then t:=[Ug[1],Ug[3],l]; fi;
	       iso  := GroupHomomorphismByImagesNC(U,Upc,t,MinimalGeneratingSet(Upc));
	       pcg  := PcgsByPcSequence(FamilyObj(One(Upc)),List(t,x->Image(iso,x)));
	       mat  := List(t,x-> ExponentsOfPcElement(pcg,Image(iso,x^g)))*One(GF(p));
               k    := SolutionMat(mat-mat^0,[0,0,1]*One(GF(p)));
	       h    := SolutionMat(mat-mat^0,k);
	       k    := PreImagesRepresentative(iso,PcElementByExponents(pcg,List(k,Int)));
	       h    := PreImagesRepresentative(iso,PcElementByExponents(pcg,List(h,Int)));
	       gen_final := [g,h,k,l];
	       im_final  := [Gstd.1,Gstd.2,Gstd.3,Gstd.4];


            else   ### last two cases, [p^4,9] and [p^4,10]

               sz   := p^4;
               U    := Centraliser(G,FrattiniSubgroup(G)); #p^2 x p
	       h    := First(GeneratorsOfGroup(U),x->Order(x)=p^2);
               g    := Filtered(GeneratorsOfGroup(G),x-> not x in U);
	       hh   := First(g,x->Order(x)=p);
	       if not hh = fail then
	          g := hh;
	       else
	          g    := g[1];
		  l    := h^p;
                  want := g^p;
                  i    := First([0..p-1],x-> l^x=want);
		  g    := g*h^-i;
	       fi;

               ## need to find correct power of g that allows us to define
	       ## h of order p^2 and then k = h^-1*h^g such that k^g=h^p*k for id 9 and
	       ## k^g = h^(Z(p)^-1 * p)*k for id 10

	       i   := 0;
	       i9  := fail;
	       i10 := fail;
	       hh  := h^p*h^-1;
	       hh2 := h^(Int(Z(p)^-1)*p)*h^-1;
	       repeat
                  gg := g^i;
		  if (h^-1*h^(gg))^(gg)= hh*h^(gg) then
		     i9:=i;
		  elif (h^-1*h^(gg))^(gg)= hh2*h^(gg) then
		     i10:=i;
		  fi;
                  i := i+1;
               until i>=p or not i9=fail or not i10=fail;

	       if not i9 = fail then
	          id   := [sz,9];
		  Gstd := SmallGroup(id);
		  g         := g^i9;
		  gen_final := [g,h,h^-1*h^g,h^p];
	          im_final  := [Gstd.1,Gstd.2,Gstd.3,Gstd.4];
	       elif not i10 = fail then
		   id   := [sz,10];
	  	   Gstd := SmallGroup(id);
		   g    := g^i10;
		   gen_final := [g,h,h^-1*h^g,h^(Int(Z(p)^-1)*p)];
	           im_final  := [Gstd.1,Gstd.2,Gstd.3,Gstd.4];
	       else Error("should not happen"); fi;


            fi;


         fi;

      fi;

   fi;

   if test = true then
      Display(" ... done; now construct isomorphism with test (no NC)");
      iso := GroupHomomorphismByImages(G,Gstd,gen_final,im_final);
   else
      iso := GroupHomomorphismByImagesNC(G,Gstd,gen_final,im_final);
   fi;

   if iso = fail then Error("oops... something is wrong for ",IdSmallGroup(G)); fi;
   if not iso = 0 then return rec(id := id, iso:=iso); fi;

   Display ("this case is not covered yet");
   return fail;
end;






#####################################################################################
#####################################################################################
#####################################################################################
#####################################################################################
#####################################################################################
##
##
## Now do the constant classes for p^5
##
##


p5id_profiles := function(G)
local lcs, lps;

   if Size(G) = 1 then return [[0],[0]]; fi;
   lcs := List(Filtered(LowerCentralSeries(G),y-> Size(y)>1),x->Collected(FactorsInt(Size(x)))[1][2]);
   Add(lcs,0);
   lps := List(Filtered(PCentralSeries(G),y-> Size(y)>1),x->Collected(FactorsInt(Size(x)))[1][2]);
   Add(lps,0);
   return [lps,lcs];
end;





#####################################################################################
## Identification function for groups G of size p^5 that lie in a log-sequence family
## of constant size
## input:  group G and ls = [lps, lcs]
## output: group ID
##
p5id_idp5_constant := function(G,ls)
   local p, iso, getspecialmax1, getspecialmax2, getspecialfact, singleton, constant,
   pos, startid, nr, e, U, c, els, d, hom, Q, idp4, gen, DB, z, g, C, h, mat, myf, id,
   a, b, i, done, aa, bb, dd, ee, cc, frs, u, gz, w, snd, v;

   p := PrimePGroup(G);
   iso := fail;

   ## helping function for G20, G21, G25, G25
   ## construct ID of preimage of nonab max in G/G'\cap G^p
   getspecialmax1 := function(H, abl)
      local F, hom, gens, HQ, iso, id;
      F   := Intersection(DerivedSubgroup(H),Agemo(H,PrimePGroup(H)));
      hom := NaturalHomomorphismByNormalSubgroupNC(H,F);
      HQ  := Image(hom);
      iso := p5id_p4IsoStandard(HQ).iso;
      if abl then
         gens := GeneratorsOfGroup(Image(iso)){[2,3,4]};
      else
         gens := GeneratorsOfGroup(Image(iso)){[1,2,4]};
      fi;
      gens := List(gens,x-> PreImagesRepresentative(hom,PreImagesRepresentative(iso,x)));
      Add(gens,MinimalGeneratingSet(F)[1]);
      HQ  := Subgroup(H,gens);
      id := p5id_p4IsoStandard(HQ);
      if not abl or id.id[2] = 14 then
         return id;
      elif id.id[2] <> 14 then
         gens := GeneratorsOfGroup(Image(iso)){[1,3,4]};
         gens := List(gens,x-> PreImagesRepresentative(hom,PreImagesRepresentative(iso,x)));
         Add(gens,MinimalGeneratingSet(F)[1]);
         HQ  := Subgroup(H,gens);
         id := p5id_p4IsoStandard(HQ);
         return id;
      fi;
   end;

   getspecialmax2 := function(H)
      local p, F, hom, HQ, iso, gens, id;
      p := PrimePGroup(H);
      F   := Intersection(DerivedSubgroup(H), Center(H));
      hom := NaturalHomomorphismByNormalSubgroupNC(H,F);
      HQ  := Image(hom);
      iso := p5id_p4IsoStandard(HQ).iso;
      gens := GeneratorsOfGroup(Image(iso)){[2,3,4]};
      gens := List(gens,x -> PreImagesRepresentative(hom,PreImagesRepresentative(iso,x)));
      gens:= Concatenation(gens,MinimalGeneratingSet(F));
      HQ  := Subgroup(H,gens);
      id := p5id_p4IsoStandard(HQ);
      return id;
   end;

   getspecialfact := function(H)
      local p, C, gens, i, id;
      p := PrimePGroup(H);
      C   := Center(H);
      gens := SmallGeneratingSet(C);
      id := p5id_p4IsoStandard(H/Subgroup(H, [gens[1]]));
      if id.id = [p^4, 3] then
         id := p5id_p4IsoStandard(H/Subgroup(H, [gens[2]]));
      fi;
      return id;
   end;

   ### the ls where the families are singletons
   singleton := [ [[5, 0], [5, 0]], [[5, 1, 0], [5, 0]], [[5, 2, 0], [5, 0]],
                  [[5, 2, 1, 0], [5, 0]], [[5, 3, 0], [5, 1, 0]],
                  [[5, 3, 1, 0], [5, 0]], [[5, 3, 2, 1, 0], [5, 0]],
                  [[5, 3, 2, 1, 0], [5, 1, 0]], [[5, 4, 3, 2, 1, 0], [5, 0]] ];

   ### the ls where the families are constant but not singletons
   constant :=  [ [[5,1,0], [5,1,0], 5], [[5,2,0],[5,1,0], 5],
                  [[5,2,1,0],[5,1,0], 2], [[5,2,1,0],[5,2,1,0], 10],
                  [[5,3,1,0], [5,1,0], 3], [[5,3,1,0], [5,2,1,0], 9]];

   pos := Position(singleton,ls);
   if not pos=fail then return rec(id:=[1,2,8,14,27,28,41,42,43][pos],iso:=fail); fi;

   pos := Position(List(constant,u->u{[1,2]}),ls);
   if pos = fail then Error("should not happen"); fi;
   startid  := [2,8,14,16,28,31][pos]; #add position of group to this

   if pos = 1 then
      nr := Position([[p,3], [p,1], [p^2,3], [p^2,2], [p^2,1]],[Exponent(G),RankPGroup(Centre(G))]);

      if nr = 4 and false then #####type 68
         #68  --> our G_6 (Exponent (p^2, RankPGroup(Centre(G)) = (p^2,2)(
         # NEED b^a=be, c^p=e
         e := MinimalGeneratingSet(Agemo(G,p))[1];
         U := Subgroup(G,[e]);
         c := First(Pcgs(Centre(G)),x->x^p in U);
         e := c^p;
         U := Subgroup(G,[c]);
         els := List(Pcgs(Omega(Center(G),p)),x->x);
         Add(els,els[1]*els[2]);
         d := First(els,x-> p5id_p4IsoStandard(G/Subgroup(G,[x])).id=[p^4,14]);
         hom := NaturalHomomorphismByNormalSubgroup(G,Subgroup(G,[d]));
         Q   := Image(hom);
         idp4 := p5id_p4IsoStandard(Q);
         if not idp4.id = [p^4,14] then Error("wrong id quotient"); fi;
         iso := idp4.iso;
         gen := List(GeneratorsOfGroup(Image(iso)),x->PreImagesRepresentative(iso,x));
         gen := List(gen,x->PreImagesRepresentative(hom,x));
         DB  := SmallGroup(p^5,IdSmallGroupFromType_p5(p,68));
         iso := GroupHomomorphismByImagesNC(G,DB,[gen[1],gen[2],gen[3],d,gen[4]],Pcgs(DB));
         if iso=fail then Error("iso false");  fi;
      fi;

      if nr = fail then Error("should not happen"); fi;
      return rec(id:=startid + nr, iso:=iso);
   fi;

    if pos = 2 then
      z  := Centre(G);
      nr := Position([[p^2,p],[p,p],[p,p^2],[p^2,p^2]], [Exponent(z),Size(Agemo(G,p))]);

      if nr = fail then Error("should not happen"); fi;

      if nr in [1,2,3] then return rec(id:=startid + nr, iso:=fail); fi;

      startid := startid+3;
      #now distinguish the two groups C_p \ltimes (C_{p^2} x C_{p^2})

      nr := Position([[p^4, 11], [p^4, 13]],
            p5id_p4IsoStandard(G/Agemo(Center(G),p)).id);
      return rec(id:=startid+nr,iso:=fail);

      g := First(GeneratorsOfGroup(G),x->Order(x)=p^2);
   fi;

   if pos = 3 then
      if Exponent(Centre(G))=p^3 then
         return rec(id:=startid + 1, iso:=fail);
      else
         return rec(id:=startid + 2, iso:=fail);
      fi;
   fi;

   myf :=2;
   if pos = 4 then
      if Size(Centre(G))=p^2 then ##types 54,55,56,57,58
         if IsCyclic(Centre(G)) then return rec(id:=startid + 2, iso:=fail); fi; #55
         if Size(Agemo(G,p))=1 then return rec(id:=startid + 1, iso:=fail); fi;  #54
         if IsElementaryAbelian(Centraliser(G,DerivedSubgroup(G))) then
                return rec(id:=startid + 3, iso:=fail); #56
         fi;

         ## now it remains to differntiate 57 and 58: these have different actions (use smaller group ID?)
         ## 57 has (p^4,10) but no (p^4,9), and 58 is vice versa
         id := getspecialmax1(G, false);
         if id.id = [p^4,10] then return rec(id:=startid + 4, iso:=fail);
         elif id.id=[p^4,9] then return rec(id:=startid + 5, iso:=fail);
         else Error("arg!"); fi;

      else #center=p and 59,60,61,62,63
         if Size(Agemo(G,p))=1 then return rec(id:=startid + 6, iso:=fail); fi; #59
         if Exponent(Centraliser(G,DerivedSubgroup(G)))=p then
            return rec(id:=startid + 8, iso:=fail); #61
         fi;

         ## now it remains to differntiate 62, 63: these have different actions (use smaller group ID?)
         id := getspecialmax1(G, true);
         if id.id = [p^4,14] then return rec(id:=startid + 7, iso:=fail); fi; #60

         ### 62 has (p^4,10) but no (p^4,9), and 63 is vice versa
         id := getspecialmax1(G, false);

         if id.id = [p^4,10] then return rec(id:=startid + 9, iso:=fail);
         elif id.id = [p^4,9] then return rec(id:=startid + 10, iso:=fail);
         else Error("arg"); fi;

      fi;
   fi;

   if pos = 5 then
      nr := Position([[p^3,p^2],[p^2,p^3],[p^3,p^3]], [Size(Agemo(G,p)),Exponent(G/DerivedSubgroup(G))]);
      return rec(id:=startid + nr, iso:=fail);
   fi;

   if pos = 6 then
      if AbelianInvariants(Agemo(G, p)) = [p] then
         id := getspecialmax2(G);
         if id.id = [p^4, 15] then
            return rec(id:=startid+1,iso:=fail); #16
         elif id.id = [p^4, 12] then
            return rec(id:=startid + 5,iso:=fail); #20
         fi;

      elif AbelianInvariants(Agemo(G,p)) = [p,p] then
         id := getspecialmax2(G);
         if id.id = [p^4, 13] then
            return  rec(id:=startid+6,iso:=fail); #21
         fi;

         id := getspecialfact(G);
            if id.id = [p^4,9] then
               return rec(id:=33,iso:=fail); #17
            elif id.id = [p^4,10] then
               return rec(id:=34,iso:=fail); #18
            fi;

      elif AbelianInvariants(Agemo(G,p)) = [p,p^2] then
         return rec(id:=startid+9,iso:=fail); #24

      elif AbelianInvariants(Agemo(G,p)) = [p^2] then
         id := getspecialmax2(G);
         if id.id = [p^4, 11] then
            return rec(id:=startid+4,iso:=fail); #19
         fi;

         #now it remains to distinguish 22 and 23
         U   := Agemo(Centre(G),p);
         gz   := MinimalGeneratingSet(Centre(G))[1];
         hom := NaturalHomomorphismByNormalSubgroup(G,U);
         iso := p5id_p4IsoStandard(Image(hom)).iso;

         ##Display("start auts");
         ##for alp in AutomorphismGroup(Image(iso)) do

         gen := List(GeneratorsOfGroup(Image(iso)),x->PreImagesRepresentative(iso,x));
         gen := List(gen,x->PreImagesRepresentative(hom,x));
         w   := gen[2]^p;
         if not w=w^0 then
            i:=First([1..p^2-1],x->(gz^(p*x)=w)); gen[2] := gen[2]*gz^-i;
         fi;
         w   := gen[3]^p;
         if not w=w^0 then
            i:=First([1..p^2-1],x->(gz^(p*x)=w)); gen[3] := gen[3]*gz^-i;
         fi;
         ## sanity check
         if not Order(gen[2])=p or not Order(gen[3])=p or not Order(gen[1])=p^3
             or not gen[3]^-1*Comm(gen[2],gen[1]) in U or not Comm(gen[3],gen[1]) in U or not Comm(gen[3],gen[2]) in U then
            Error("should not have happened");
         fi;

         b := gen[2];
         c := gen[3];
         a := gen[1];
         if Comm(c,a)=One(G) then a:=a*b; fi;
         d := a^p; e:= d^p;

         done := false;
         i    := 0;
         aa   := One(G);
         while not done do
            i  := i+1;
            aa := aa*a; ##a^i
            bb := b;
            dd := aa^p;
            ee := dd^p;
            cc := Comm(bb,aa);
            frs := Comm(cc,aa);
            snd := Comm(cc,bb);
            u  := First([1..p-1],x-> frs=ee^x);
            v  := First([1..p-1],x-> snd=ee^x);
            if u=v then done := true; a:=aa; b:=bb; c:=cc; d:=dd; e:=ee; fi;
            if i > p^3 then Error("mhmm... this should not have happened"); fi;
         od;

         if (u*One(GF(p)))^((p-1)/2)=One(GF(p)) then
            return rec(id:=38,iso:=fail);
         else
            return rec(id:=39,iso:=fail);
         fi;
      fi;
   fi;

   return true;
end;



#####################################################################################
#####################################################################################
#####################################################################################
#####################################################################################
#####################################################################################
##
##
## Now do the non-constant classes for p^5
##
##



#####################################################################################
## Creates the p-cover for a given prime and family of groups
## input:  prime p, integer fam (16, 17, 18)
## output: the p-cover for the respective family
##
p5id_getPCover := function(p, fam)
    local F, gens, R, i, j;

    if fam = 6 then
        F := FreeGroup(9);
        gens := GeneratorsOfGroup(F);

        R := [F.1^p/F.4, F.2^p/F.5, F.3^p/F.6,
              Comm(F.2,F.1)/F.7, Comm(F.3,F.1)/F.8, Comm(F.3,F.2)/F.9];

        for i in [4..9] do Add(R, gens[i]^p); od;

        for i in [4..9] do
            for j in [1..i-1] do
                Add(R, Comm(gens[i], gens[j]));
            od;
        od;

    elif fam = 14 then
        F := FreeGroup(7);
        gens := GeneratorsOfGroup(F);

        R := [F.1^p/F.4, F.2^p/F.5,
              Comm(F.2,F.1)/F.3, Comm(F.3,F.1)/F.6, Comm(F.3,F.2)/F.7];

        for i in [3..7] do Add(R, gens[i]^p); od;

        for i in [4..7] do
            for j in [1..i-1] do
                Add(R, Comm(gens[i], gens[j]));
            od;
        od;

    elif fam = 17 then
        F := FreeGroup(8);
        gens := GeneratorsOfGroup(F);

        R := [F.1^p/F.5, F.2^p/F.6, Comm(F.2,F.1)/F.3,
            Comm(F.3,F.1)/F.4, Comm(F.3,F.2)/F.7, Comm(F.4, F.1)/F.8,
            Comm(F.4, F.2), Comm(F.4, F.3)];

        for i in [3..8] do Add(R, gens[i]^p); od;

        for i in [5..8] do
            for j in [1..i-1] do
                Add(R, Comm(gens[i], gens[j]));
            od;
        od;

    else
        Error("Only implemented for families 6, 14 and 17");
    fi;

   return PcGroupFpGroup(F/R);
end;



#####################################################################################
## Returns a matrix that operates on the allowable subspaces of family
## input:  prime p, integer fam (16, 17, 18), either element of GL(3,p) (fam=16),
##                  elementof of GL(2,p) (fam=17) or [x,y,z] with 1<=x,y<p, 0<=z<p
## output: matrix
##
p5id_famMats := function(p, fam, arg)
    local m, M, v;
    if fam = 6 then
        m := arg;
        if Rank(m) < 3 then Print("Warning, singular matrix"); fi;
        M := ZeroMatrix(6, 6, m);
        M{[1..3]}{[1..3]} := m;
        M[4][4] := m[1][1]*m[2][2]-m[1][2]*m[2][1];
        M[4][5] := m[1][1]*m[2][3]-m[1][3]*m[2][1];
        M[4][6] := m[1][2]*m[2][3]-m[1][3]*m[2][2];
        M[5][4] := m[1][1]*m[3][2]-m[1][2]*m[3][1];
        M[5][5] := m[1][1]*m[3][3]-m[1][3]*m[3][1];
        M[5][6] := m[1][2]*m[3][3]-m[1][3]*m[3][2];
        M[6][4] := m[2][1]*m[3][2]-m[2][2]*m[3][1];
        M[6][5] := m[2][1]*m[3][3]-m[2][3]*m[3][1];
        M[6][6] := m[2][2]*m[3][3]-m[2][3]*m[3][2];

    elif fam = 14 then
        m := arg;
        M := ZeroMatrix(4, 4, m);
        M{[1,2]}{[1,2]} := m;
        M{[3,4]}{[3,4]} := DeterminantMat(m)*m;

    elif fam = 17 then
        v := arg*Z(p)^0;
        if v[1]*Z(p) = 0*Z(p) or v[2]*Z(p) = 0*Z(p) then
            Error("v[1] and v[2] must be inversable");
        fi;
        M := ZeroMatrix(GF(p), 4, 4);
        M[1][1] := v[1];
        M[2][2] := v[2];
        M[1][2] := v[3];
        M[3][3] := M[1][1]*M[2][2]^2;
        M[4][4] := M[1][1]^3*M[2][2];
    fi;

    return M*Z(p)^0;
end;




#####################################################################################
## Determines the type of the group corresponding to the provided dual base of an
## allowed subpace of family 16
## input: a base of the dual of an allowed subspace. Must be in RREF
## output: the corresponding type, either a single integer or a list of two integers
##
p5id_fam6id := function(base)
    local p, r, trans, type, ps, can, eig, TD, k, B;

    p := Characteristic(base);
    r := RankMat(base{[1,2]}{[1..3]});
    trans := IdentityMatrix(GF(p), 6);
    can := base;

    if r = 0 then
        type := 34;

    elif r = 1 then

        ps := Last([1..3], i -> base[1][i] <> Zero(GF(p)));
        if ps = 1 then
            trans := p5id_famMats(p, 6, ([[0,1,0],[0,0,1], can[1]{[1..3]}]*Z(p)^0)^-1);
        elif ps = 2 then
            trans := p5id_famMats(p, 6, ([[1,0,0],[0,0,1], can[1]{[1..3]}]*Z(p)^0)^-1);
        else
            trans := p5id_famMats(p, 6, ([[1,0,0],[0,1,0], can[1]{[1..3]}]*Z(p)^0)^-1);
        fi;

        can := RREF(base*trans);

        if can[1][4] <> 0*Z(p)^0 then
            type := 39;

        elif can[2][4] <> 0*Z(p)^0 then
            type := 36;

        elif can{[1,2]}[4] = [0,0]*Z(p)^0 then
            type := 38;
        fi;

    elif r = 2 then

        ps := First(Tuples([1..3],2), t -> base[1][t[1]] <> 0*Z(p) and base[2][t[2]] <> 0*Z(p));
        if not 1 in ps then
            trans := p5id_famMats(p, 6, [[1,0,0]*Z(p)^0, can[1]{[1..3]}, can[2]{[1..3]}]^-1);
        elif not 2 in ps then
            trans := p5id_famMats(p, 6, [[0,1,0]*Z(p)^0, can[1]{[1..3]}, can[2]{[1..3]}]^-1);
        else
            trans := p5id_famMats(p, 6, [[0,0,1]*Z(p)^0, can[1]{[1..3]}, can[2]{[1..3]}]^-1);
        fi;
        can := RREF(base * trans);

        eig := Eigenvalues(GF(p), can{[1,2]}{[4,5]});

        if Size(eig) = 0 then
            TD := TraceMat(can{[1,2]}{[4,5]})^2/DeterminantMat(can{[1,2]}{[4,5]});
            if TD = 0*Z(p) then
               type := 49;
            else
               k := (1+DLog(Z(p), Z(p)^0-4*Z(p)^0/(TD)))/2;
               type := [50, k];
            fi;

        elif Size(eig) = 1 then
            if eig[1] = 0*Z(p) then
               type := 41;
            elif can{[1,2]}{[4,5]} = can[1][4]*[[1,0],[0,1]] then
               type := 44;
            else
               type := 46;
            fi;

        else
            if 0*Z(p) in eig then
               type := 42;
            else
               k := DLog(Z(p), eig[2]/eig[1]);
               if k > (p-1)/2 then k := -k mod (p-1); fi;
               type := [48, k];
            fi;
        fi;
    else
        Error("No mathcing type found in family (6)");
    fi;
    return type;
end;



#####################################################################################
## Calculates the transversal element (a matrix) that maps the provided base to the
## canonical dual base of the given type from family 16
## input: the type (either an integer or a pair of integers) and the starting base
## output: a matrix
##
p5id_fam6trans := function(type, base)
    local p, trans, x, y, ps, can, c, d, ab, z, pot;

    p := Characteristic(base);
    trans := IdentityMatrix(GF(p), 6);

    if type = 34 then

        if base{[1,2]}{[4,5,6]} = [[0,1,0],[0,0,1]]*Z(p)^0 then
            trans := trans;

        elif base{[1,2]}{[4,5]} = [[1,0],[0,1]]*Z(p)^0 then
            x := base[1][6];
            y := base[2][6];
            if x <> 0*Z(p) and y <> 0*Z(p) then
                trans := [[0,x,0,0,0,0],[1,y,0,0,0,0],[-x^-1,-y/x,1,0,0,0],
                    [0,0,0,-x,0,0],[0,0,0,1,0,x],[0,0,0,0,1,y]] * Z(p)^0;
            elif x <> 0*Z(p) then
                trans := [[0,x,0,0,0,0], [1,0,0,0,0,0], [-x^-1,0,1,0,0,0],
                    [0,0,0,-x,0,0], [0,0,0,1,0,x], [0,0,0,0,1,0]] * Z(p)^0;
            elif y <> 0*Z(p) then
                trans := [[0,-y,0,0,0,0], [0,0,-y,0,0,0], [y^-1,1,0,0,0,0],
                    [0,0,0,0,0,y^2], [0,0,0,1,0,0], [0,0,0,0,1,y]] * Z(p)^0;
            else
                trans := [[0,1,0,0,0,0], [0,0,1,0,0,0], [-1,0,0,0,0,0],
                    [0,0,0,0,0,1], [0,0,0,1,0,0], [0,0,0,0,1,0]] * Z(p)^0;
            fi;

        elif base{[1,2]}{[4,6]} = [[1,0],[0,1]]*Z(p)^0 then
            x := base[1][5];
            if x <> 0*Z(p) then
                trans := [[1,0,0,0,0,0], [0,x^-1,0,0,0,0], [0,1,x,0,0,0],
                    [0,0,0,x^-1,0,0], [0,0,0,1,x,0], [0,0,0,0,0,1]] * Z(p)^0;
            else
                trans := [[1,0,0,0,0,0], [0,0,-1,0,0,0], [0,1,0,0,0,0],
                    [0,0,0,0,-1,0], [0,0,0,1,0,0], [0,0,0,0,0,1]] * Z(p)^0;
            fi;
        else
            Error("This should not be possible");
        fi;

        trans := trans^-1;

    elif type in [36, 38, 39] then

        ps := Last([1..3], i -> base[1][i] <> Zero(GF(p)));
        if ps = 1 then
            trans := p5id_famMats(p, 6, ([[0,1,0],[0,0,1], can[1]{[1..3]}]*Z(p)^0)^-1);
        elif ps = 2 then
            trans := p5id_famMats(p, 6, ([[1,0,0],[0,0,1], can[1]{[1..3]}]*Z(p)^0)^-1);
        else
            trans := p5id_famMats(p, 6, ([[1,0,0],[0,1,0], can[1]{[1..3]}]*Z(p)^0)^-1);
        fi;

        can := RREF(base*trans);

        if type = 36 then
            c := can[1][5];
            d := can[1][6];

            ab := Filtered(Tuples([0..p-1]*Z(p)^0, 2), t -> t[1]*d-t[2]*c = can[2][4]);

            for y in [0..p-1]*Z(p)^0 do
                for z in [0..p-1]*Z(p)^0 do
                    pot := Filtered(ab, t -> t[1]*y-c*z = can[2][5]);
                    if Size(pot) = 0 then continue; fi;

                    pot := Filtered(pot, t -> t[2]*y-d*z = can[2][6]);
                    if Size(pot) <> 0 then
                        ab := pot;
                        break;
                    fi;
                od;
            od;

            trans := trans * p5id_famMats(p, 6, [[ab[1][1], ab[1][2], z],
                        [c, d, y], [0,0,1]]*Z(p)^0)^-1;

        elif type = 38 then
            trans := trans * p5id_famMats(p, 6, [[can[2][5], can[2][6], 0],
                                [can[1][5], can[1][6], 0], [0,0,1]]*Z(p)^0)^-1;
        elif type = 39 then
            c := Z(p)^0;
            d := can[2][6];

            ab := Filtered(Tuples([0..p-1]*Z(p)^0, 2), t -> t[1]*d-t[2]*c = can[1][4]);

            for y in [0..p-1]*Z(p)^0 do
                for z in [0..p-1]*Z(p)^0 do
                    pot := Filtered(ab, t -> t[1]*y-c*z = can[1][5]);
                    if Size(pot) = 0 then continue; fi;

                    pot := Filtered(pot, t -> t[2]*y-d*z = can[1][6]);
                    if Size(pot) <> 0 then
                        ab := pot;
                        break;
                    fi;
                od;
            od;

            trans := List(ab, t-> trans * p5id_famMats(p, 6, [[t[1], t[2], z],
                            [c, d, y], [0,0,1]]*Z(p)^0)^-1);
        else
            Error();
        fi;

    else
        ps := First(Tuples([1..3],2), t -> [base[1][t[1]], base[2][t[2]]] <> [0, 0] * Z(p));

        if not 1 in ps then
            trans := p5id_famMats(p, 6, [[1,0,0]*Z(p)^0, can[1]{[1..3]}, can[2]{[1..3]}]^-1);
        elif not 2 in ps then
            trans := p5id_famMats(p, 6, [[0,1,0]*Z(p)^0, can[1]{[1..3]}, can[2]{[1..3]}]^-1);
        else
            trans := p5id_famMats(p, 6, [[0,0,1]*Z(p)^0, can[1]{[1..3]}, can[2]{[1..3]}]^-1);
        fi;
        can := RREF(base * trans);

        trans := fail;
    fi;
    return trans;
end;



#####################################################################################
## Determines the type of the group corresponding to the provided base of an
## allowed subpace of family 17
## input: a base of the dual of an allowed subspace. Must be in RREF
## output: the corresponding type, either a single integer or a list of two integers
##
p5id_fam14id := function(base)
    local p, B, type, k, i, a, b, eig, C, bd, ac, acbd, TD;

    p := Characteristic(base);
    B := base{[1,2]}{[3,4]};

    if Rank(B) = 0 then
        type := 3;

    elif Rank(B) = 1 then

        if B[1][1] <> -B[2][2] then
            type := 4;
        else

            if B[1][2] <> 0*Z(p) then
               i := DLog(Z(p)^2, B[1][2]);
            else
               i := DLog(Z(p)^2, -B[2][1]);
            fi;

            if i <> fail then
               type := 5;
            else
               type := 6;
            fi;
        fi;

    elif Rank(B) = 2 then

        eig := Eigenvalues(GF(p), B);

        if Size(eig) = 0 then
           TD := TraceMat(B)^2/DeterminantMat(B);
           if TD = 0*Z(p) then
             type := 10;
           else
             k := (1+DLog(Z(p), Z(p)^0-4*Z(p)^0/(TD)))/2;
             type := [12, k];
           fi;

        elif Size(eig) = 1 then
            if B = B[1][1]*[[1,0],[0,1]] then
               type := 7;
            else
               if B[1][2] <> 0*Z(p) then
                  i := DLog(Z(p)^2, B[1][2]);
               else
                  i := DLog(Z(p)^2, -B[2][1]);
               fi;

               if i <> fail then
                  type := 8;
               else
                  type := 9;
               fi;
            fi;
        else
            TD := TraceMat(B)^2/DeterminantMat(B);
            k := DLog(Z(p), eig[2]/eig[1]);
            if k > (p-1)/2 then k := -k mod (p-1); fi;
            type := [11, k];
        fi;
    else
        Error("No matching type found in family (14)");
    fi;

    return type;
end;



#####################################################################################
## Calculates the transversal element (a matrix) that maps the provided base to the
## canonical base of the given type from family 17
## input: the type (either an integer or a pair of integers) and the starting base
## output: a matrix
##
p5id_fam14trans := function(type, base)
    local p, B, trans, k, i, a, b;

    p := Characteristic(base);
    B := base{[1,2]}{[3,4]};
    trans := IdentityMatrix(GF(p), 4);

    if type = 3 then

    elif type in [5, 6] then
        if B[1][2] = 0*Z(p) then
            trans := trans*p5id_famMats(p, 14, [[0,1],[1,0]]*Z(p)^0);
            B := RREF(base*trans){[1,2]}{[3,4]};
        fi;
        if type = 5 then
            k := 0;
        else
            k := 1;
        fi;

        i := DLog(Z(p)^2, B[1][2]/Z(p)^k);
        b := Z(p)^i;
        i := DLog(Z(p)^2, -B[2][1]/Z(p)^k);
        if i <> fail then
            a := Z(p)^i;
        else
            a := 0*Z(p);
        fi;

        trans := trans*p5id_famMats(p, 14, [[0,-b],[b^-1,a]]*Z(p)^0);

    elif type = 4 then
        trans := fail;
    elif type = 7 then
        trans := p5id_famMats(p, 14, [[B[1][1]^-1, 0], [0,1]]*Z(p)^0);

    elif type in [8, 9] then
        if B[1][2] = 0*Z(p) then
            trans := trans*p5id_famMats(p, 14, [[0,1],[1,0]]*Z(p)^0);
            B := RREF(base*trans){[1,2]}{[3,4]};
        fi;

        if type = 8 then
            k := 0;
        else
            k := 1;
        fi;

        i := DLog(Z(p)^2, B[1][2]/Z(p)^k);
        b := Z(p)^i;
        i := DLog(Z(p)^2, -B[2][1]/Z(p)^k);
        if i <> fail then
            a := Z(p)^i;
        else
            a := 0*Z(p);
        fi;

    elif type = 10 then
        trans := fail;
    elif IsList(type) and type[1] = 11 then
        k := type[2];
        trans := fail;

    elif IsList(type) and type[1] = 12 then
        k := type[2];
        trans :=  fail;

    else
        Error("No such type among groups of family 14.");
    fi;

    return trans;
end;



#####################################################################################
## Determines the type of the group corresponding to the provided dual base of an
## allowed subpace of family 18
## input: a base of the dual of an allowed subspace. Must be in RREF
## output: the corresponding type, either a single integer or a list of two integers
##
p5id_fam17id := function(base)
    local p, ps, type, k, i;

    p := Characteristic(base);
    ps := Positions(base[1], 0*Z(p));

    if ps = [1,2,3] then
        type := 28;
    elif ps = [1,3] or ps = [3] then
        type := 29;
    elif ps = [2,3] then
        type := 30;
    elif ps = [1,2] then
        type := 31;
    elif ps = [1] or ps = [] then
        type := 32;
    elif ps = [2] then
        type := 33;
    else
        Error("No matching type found in family (17)");
    fi;

    if type in [29, 32] then
        for k in [1..3] do
            i := DLog(Z(p)^3, (base[1][4]/base[1][2])/Z(p)^k);
            if i <> fail then break; fi;
        od;
        if i = fail then Error("No matching parameter for type"); fi;
        type := [type, k];

    elif type = 33 then
        for k in [1..4] do
            i := DLog(Z(p)^4, base[1][3]/base[1][4]^2*Z(p)^k);
            if i <> fail then break; fi;
        od;
        if i = fail then Error("No matching parameter for type"); fi;
        type := [type, k];
    fi;

    return type;
end;



#####################################################################################
## Calculates the transversal element (a matrix) that maps the provided base to the
## canonical dual base of the given type from family 18
## input: the type (either an integer or a pair of integers) and the starting base
## output: a matrix
##
p5id_fam17trans := function(type, base)
    local p, can, trans, k, i, a, b;

    p := Characteristic(base);
    can := [ShallowCopy(base[1])];

    trans := IdentityMatrix(4,base);

    #If first and second entry are non-zero, we can get first = 0 and second = 1
    if base[1][1] = Z(p)^0 and base[1][2] <> 0*Z(p) then
        trans := TransposedMat(p5id_famMats(p, 17,
                                [1, base[1][2]^-1, -base[1][2]^-1]));
    fi;
    #Now every can is either [0,0,...] or [1,0,...] or [0,1,...]

    if type = 28 then
        trans := trans;

    elif type = 31 then
        a := can[1][4];
        trans := trans * TransposedMat(p5id_famMats(p, 17, [1,a,0]));

    elif type = 30 then
        a := can[1][4];
        trans := trans * TransposedMat(p5id_famMats(p, 17, [1,a^-1,0]));

    elif IsList(type) and type[1] = 29 then

        k := type[2];
        i := DLog(Z(p)^3, can[1][4]/Z(p)^k);
        if i = fail then Error("Type 29"); fi;

        a := Z(p)^i;
        trans := trans * TransposedMat(p5id_famMats(p, 17, [a^-1,1,0]));

    elif IsList(type) and type[1] = 32 then

        k := type[2];
        i := DLog(Z(p)^3, can[1][4]/Z(p)^k);
        if i = fail then Error("Type 32"); fi;

        a := Z(p)^i;
        b := can[1][3]/(a*Z(p)^k);
        trans := trans * TransposedMat(p5id_famMats(p, 17, [a^-1,b^-1,0]));

    elif IsList(type) and type[1] = 33 then

        k := type[2];
        i := DLog(Z(p)^4, can[1][3]/can[1][4]^2*Z(p)^k);
        if i = fail then Error("Type 33"); fi;

        a := Z(p)^-i;
        b := can[1][4]/(a^2*Z(p)^k);
        trans := trans * TransposedMat(p5id_famMats(p, 17, [a^-1,b^-1,0]));
    else
        Error("No such type among groups of family 17.");
    fi;
    return trans;
end;




#####################################################################################
## Setup for the orbit calculation and search for canonical represantatives
## input:  group G, prime p, integer fam (16, 17, 18)
## output: record with necessary and useful stuff
##
p5id_setupRepsSearch := function(G, p, fam)
    local PCS, nathom, iota, iotaInv, H, C, gensC, phi, gensG, pcgsM, mats,
    rho, U, base, dual;

    PCS := PCentralSeries(G);

    #Set up p-Cover of canonical group isomorphic to G/lam(G)
    nathom := NaturalHomomorphismByNormalSubgroup(G, PCS[Size(PCS)-1]);
    iota := p5id_p4IsoStandard(Image(nathom));
    iotaInv := InverseGeneralMapping(iota.iso);
    H := Image(iota.iso);

    if fam = 6 then
        mats := List(GeneratorsOfGroup(GL(3,p)), g -> p5id_famMats(p, fam, g));
    elif fam = 14 then
        mats := List(GeneratorsOfGroup(GL(2,p)), g -> p5id_famMats(p, fam, g));
    elif fam = 17 then
         mats := List([[1,Z(p),0]*Z(p)^0, [Z(p),Z(p),(p-1)*Z(p)^(2-p)]],
                      v -> p5id_famMats(p, fam, v));
    else
        Error("This should not be reachable\n");
        fam := "rest";
    fi;

    #Set up mapping from p-cover to G via G -nathom-> G/lam(G) <-iota-> H <-phi- C
    C := p5id_getPCover(p, fam);
    gensC := MinimalGeneratingSet(C);
    phi := GroupHomomorphismByImagesNC(C, H, gensC, MinimalGeneratingSet(H));
    pcgsM := Pcgs(Kernel(phi));

    #Determine suitable generators of G by preimages of Image(phi o iota, gensC)
    gensG := List([1..Rank(G)], i ->
                  PreImage(nathom, [Image(iotaInv, Image(phi, gensC[i]))])[1]);

    #Define hom. from p-cover to group and determine kernel and
    rho := GroupHomomorphismByImages(C, G, gensC, gensG);
    U := Kernel(rho);

    #Convert to vectors and dualise if useful
    base := List(Pcgs(U), g -> ExponentsOfPcElement(pcgsM, g)* Z(p)^0);

    if fam in [6, 17] then
        base := NullspaceMat(TransposedMat(base));
        mats := List(mats, x -> TransposedMat(x));
        dual := true;
    else
        dual := false;
    fi;

    base := TriangulizedMat(base);

    return rec(C := C, M := pcgsM, mats := mats, base := base, fam := fam, dual := dual);
end;



#####################################################################################
## Identification function for groups of non-constant families (6, 14, 17)
## input:  group G, prime p, profile ls
## output: pair [p^5, id]
##
p5id_iddet := function(G, p, ls, iso)
    local fam, tmp, type, trans, id, aut;

    if ls = [[5,2,0], [5,2,0]] then
        fam := 6;
    elif ls = [[5,3,2,0], [5,3,2,0]] then
        fam := 14;
    elif ls = [[5,3,2,1,0], [5,3,2,1,0]] then
        fam := 17;
    fi;

    tmp := p5id_setupRepsSearch(G, p, fam);
    trans := fail;

    if tmp.fam = 6 then
        type := p5id_fam6id(tmp.base);
        if iso then trans := p5id_fam6trans(type, tmp.base); fi;

    elif tmp.fam = 14 then
        type := p5id_fam14id(tmp.base);
        if iso then trans := p5id_fam14trans(type, tmp.base); fi;

     elif tmp.fam = 17 then
        type := p5id_fam17id(tmp.base);
        if iso then trans := p5id_fam17trans(type, tmp.base); fi;

    else
        Error("Not implemented");
    fi;

    id := IdSmallGroupFromType_p5(p, type);

    if iso and IsBound(trans) then

        aut := GroupHomomorphismByImages(Group(tmp.M), Group(tmp.M), tmp.M,
                                  List([1..Size(tmp.M)],i->PcElementByExponents(tmp.M,trans[i])));
        Error();
    fi;
    return rec(id:=[p^5, id], trans := trans);
end;




#####################################################################################
#####################################################################################
#####################################################################################
#####################################################################################
#####################################################################################



#####################################################################################
## Identification function for groups G of size dividing p^5
## input:  group G
## output: record consiting of group ID and isomorphism SmallGroup (for p^4)
##
p5id_Idp5Group := function(GG)
    local ls, param, sz, internal_id, our,type,pos,id,p, isospcgs, res, G,iso,ttt;

  
    sz := Collected(FactorsInt(Size(GG)));
    if not Size(sz)=1 or not sz[1][2]<=5 then Error("input group must have size p^5"); fi;
    p   := sz[1][1];
    iso := fail;

    isospcgs := false;
    G        := GG;
    if not HasSpecialPcgs(GG) then
        isospcgs := IsomorphismSpecialPcGroup(GG);
        G        := Image(isospcgs);
    fi;


    if sz[1][1] <= 5 then
       #Display("use IdSmallGroup and bf iso");
        ttt := rec(id := IdSmallGroup(G), iso := fail);
	if sz[1][1] in [2,3] or (sz[1][1]=5 and sz[1][2]<5) then ###brute force too slow for 5^5
      	   if not isospcgs = false then 
   	      ttt.iso := isospcgs*IsomorphismGroups(G,SmallGroup(ttt.id));
	    else
               ttt.iso := IsomorphismGroups(G,SmallGroup(ttt.id));
           fi;
	fi;   
	SetIdGroup(G,ttt.id);
	SetIdGroup(GG,ttt.id);
	return ttt;
    fi;

    if sz[1][2] <= 4 then
        res := p5id_p4IsoStandard(G);
	SetIdGroup(G,res.id);
	SetIdGroup(GG,res.id);
        if not isospcgs = false then
            res.iso := GroupHomomorphismByImagesNC(GG,Image(res.iso), GeneratorsOfGroup(GG),
                    List(GeneratorsOfGroup(GG),u->Image(res.iso,Image(isospcgs,u))));
            if res.iso = fail then Error("iso fail 1"); fi;
        fi;
        if not Source(res.iso) = GG then Error("dudeldi"); fi;
	
        return res;

    fi;

    ls    := p5id_profiles(G);

    param := [[[5,2,0],[5,2,0]], [[5,3,2,0],[5,3,2,0]], [[5,3,2,1,0],[5,3,2,1,0]]];

    if not ls in param then
        internal_id := p5id_idp5_constant(G,ls);
        if IsRecord(internal_id) then
            iso := internal_id.iso;
        if not isospcgs = false and not iso = fail then
                iso := GroupHomomorphismByImagesNC(GG,Range(iso), GeneratorsOfGroup(GG),
                    List(GeneratorsOfGroup(GG),u->Image(iso,Image(isospcgs,u))));
                if iso = fail then Error("mhmm"); fi;
            fi;
        internal_id:=internal_id.id;
        else
            internal_id:=internal_id.id;
        fi;

        if p mod 4 = 1 then
            if internal_id = 20 then internal_id := 21;
            elif internal_id = 21 then internal_id := 20; fi;

            if internal_id = 25 then internal_id := 26;
            elif internal_id = 26 then internal_id := 25; fi;
        fi;

        ##translate to GAP id

        our := [1, 2, 8, 14, 27, 28, 41, 42, 43, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40];
        type := [70, 66, 43, 51, 2, 13, 26, 27, 1, 64, 65, 67, 68, 69, 35, 37, 40, 45, 47, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 14, 15, 25, 16, 17, 18, 19, 20, 21, 22, 23, 24];

        pos := Position(our, internal_id);
        if pos = fail then Error("ops"); fi;
        id  := [p^5, IdSmallGroupFromType_p5(p,type[pos])];

    elif ls in param then
            res := p5id_iddet(G, p, ls, false);
            id := res.id;
    fi;

    SetIdGroup(G,id);
    SetIdGroup(GG,id); 
    return rec(id := id, iso := iso);
end;




#####################################################################################
#####################################################################################
#####################################################################################
#####################################################################################
#####################################################################################
#####################################################################################
##
##
## random experimental iso for groups of order p^5
##
##
#####################################################################################
#####################################################################################
#####################################################################################
#####################################################################################






#####################################################################################
#####################################################################################
##
##
## input: group G of order p^5
## output: isom G -> SmallGroup(IdSmallGroup(G))
##
## Randomised algorithm: if this fails, we return fail and one should use ANUPQ
##
## main part of this function has been coded with Claude Opus
## N.B.: returned isomorphism is always correct, but can fail
##
p5id_iso_random_bruteforce := function(G)
local id, H, C, i, j, k, gen, ord, genH, ordH, p, CH, nat, natH, Q,QH, isoQ, isoQH, iso, isos,
       im, adj, mychar,itCH,t,newim,r;

  #Print("start iso bf");

   if not HasIdGroup(G) then
      id := p5id_Idp5Group(G);
      if not id.iso=fail then return id.iso; fi;
      id := id.id;
   else
      id := IdSmallGroup(G);
   fi;
   H := SmallGroup(id);
 

   if IsAbelian(G) then
      gen := List(MinimalGeneratingSet(G),x->x);
      ord := List(gen,Order);
      SortParallel(ord,gen);
      genH :=List(MinimalGeneratingSet(H),x->x);
      ordH := List(genH,Order);
      SortParallel(ordH,genH);
      return GroupHomomorphismByImages(G,H,gen,genH);
   fi;

  ## char is always of rank at most 2; always in Phi and always el-ab!
   p    := PrimePGroup(G);
   mychar := x -> Omega(Intersection([FrattiniSubgroup(x),Centre(x),DerivedSubgroup(x)]),p);
   C    := mychar(G);
   CH   := mychar(H);

   nat  := NaturalHomomorphismByNormalSubgroup(G,C);
   natH := NaturalHomomorphismByNormalSubgroup(H,CH);
   Q    := Image(nat);
   QH   := Image(natH);

  ##Print("CONTINUE BF HERE",IdSmallGroup(G));

################################################################################# START OF CLAUDE CODE!!!!!

######## the following has been coded with the help of Claude.ai;
######## we verify the output, so the returned value will never be incorrect
   ##
   ## Isomorphism G --> H for the standard copy H = SmallGroup(p^5,i) of G.
   ##
   ## All cases rest on one lifting step. Let x_1,...,x_n be a pcgs of G, let K be an
   ## elementary abelian subgroup of Z(H) cap Phi(H), and let im[k] in H realise a given
   ## isomorphism G/K' --> H/K. A homomorphism G --> H inducing it must map
   ##      x_k --> im[k]*c_k     with   c_k in K,
   ## and the power-commutator relations of G turn this into a linear system A*X = B
   ## over GF(p), the rows of A being the exponent vectors of the relations and the rows
   ## of X the coordinates of the c_k. Here A does not depend on the isomorphism and is
   ## set up once; every solution yields an isomorphism, and unsolvability means that the
   ## given isomorphism does not lift. Variants allow a normal non-central kernel
   ## (r.liftmod), an abelian kernel of exponent p^2 (r.liftab) and a central cyclic
   ## kernel of order p^2 (r.liftcyc). Everything returned is verified.
   ##
   ## The cases are tried in this order.
   ##
    ##  (A)   Phi(G) elementary abelian and central: G is determined by the commutator
   ##        and p-power maps on V = G/Phi(G), so a compatible isomorphism V --> V' is
   ##        constructed by linear algebra and lifted.
   ##  (A2)-(A5)  rank 3 (A2,A3) and rank 2 (A4,A5): the commutator and p-power maps
   ##        between the layers of G are preserved by an isomorphism up to scalars,
   ##        which leaves O(p) candidates for the map induced on V; each candidate is
   ##        lifted, or discarded, by linear algebra.
   ##  (B)   the admissible characteristic subgroups K, smallest first (the larger the
   ##        quotient, the more it determines): the k-th subgroup of G and the k-th of H
   ##        come from the same recipe, hence correspond under every isomorphism, and
   ##        the isomorphism G/K --> H/K from the standard copies is lifted.
   ##  (B2)  the subgroups of order p of C are NOT characteristic, so there is no
   ##        canonical partner in H: we fix one such subgroup in G and try ALL p+1
   ##        candidates in H, which is complete because an isomorphism maps C onto CH.
   ##  (C)   bounded random search: modify the isomorphism of a quotient by random
   ##        automorphisms of that quotient until it lifts.
   ##

   r      := rec( pcgG := Pcgs(G), rel := [], exp := [] );
   r.n    := Length(r.pcgG);
   r.one  := One(GF(p));
   r.oneH := One(H);

   ## the relations of the pc presentation of G wrt r.pcgG: the pair [i,0] stands for
   ## the relation with left hand side x_i^p and [i,j] for the one with left hand side
   ## Comm(x_j,x_i); r.exp holds the exponent vectors of the right hand sides
   for i in [1..r.n] do
      Add(r.rel, [i,0]);
      Add(r.exp, ExponentsOfPcElement(r.pcgG, r.pcgG[i]^p));
      for j in [i+1..r.n] do
         Add(r.rel, [i,j]);
         Add(r.exp, ExponentsOfPcElement(r.pcgG, Comm(r.pcgG[j], r.pcgG[i])));
      od;
   od;
   r.mat := TransposedMat(r.one * r.exp);
   ## the exponent vectors are sparse: only these positions contribute to the products
   ## in r.liftu below, which is the innermost loop of the whole function
   r.sup  := List(r.exp, v -> Filtered([1..r.n], l -> not v[l] = 0));
   r.nrel := Length(r.rel);

   ## A*X = B is solvable if and only if v*B = 0 for every v in the left null space of
   ## A; as A does not depend on the isomorphism, that null space is computed once. The
   ## conditions are checked in r.liftu while B is built, so a hopeless candidate is
   ## discarded after a few relations, which is what makes the search in (C) cheap.
   r.left := NullspaceMat(r.one * r.exp);
   r.test := List([1..r.nrel], k -> []);
   for t in r.left do
      k := Maximum(Filtered([1..r.nrel], j -> not IsZero(t[j])));
      Add(r.test[k], rec(sup := Filtered([1..k], j -> not IsZero(t[j])), v := t));
   od;

   ## r.liftu(u,n2,K): solves the system, where u is the list of images in H/K of the
   ## pcgs of G under the isomorphism to be lifted; returns the lift G --> H, or fail.
   ## Using images rather than the map itself keeps one try in (C) cheap.
   r.liftu := function(u, n2, K)
      local pcgK, d, im, rhs, k, l, v, w, sol, c, cond, hom;
      pcgK := Pcgs(K);
      d    := Length(pcgK);
      im   := List(u, y -> PreImagesRepresentative(n2, y));
      rhs  := [];
      for k in [1..r.nrel] do
         if r.rel[k][2] = 0 then
            w := im[r.rel[k][1]]^p;
         else
            w := Comm(im[r.rel[k][2]], im[r.rel[k][1]]);
         fi;
         v := r.oneH;
         for l in r.sup[k] do v := v * im[l]^r.exp[k][l]; od;
         w := LeftQuotient(v, w);
         if not w in K then return fail; fi;
         Add(rhs, r.one * ExponentsOfPcElement(pcgK, w));
         ## discard this candidate as soon as one solvability condition fails
         for cond in r.test[k] do
            if not IsZero(Sum(cond.sup, l -> cond.v[l]*rhs[l])) then return fail; fi;
         od;
      od;

      ## solve A*X = B column by column; the k-th row of X gives the element c_k
      ## the conditions above guarantee that the system is solvable
      sol := List(TransposedMat(rhs), v -> SolutionMat(r.mat, v));
      if ForAny(sol, v -> v = fail) then return fail; fi;
      c   := List([1..r.n], k -> PcElementByExponents(pcgK,
                    List([1..d], l -> IntFFE(sol[l][k]))));
      hom := GroupHomomorphismByImages(G, H, AsList(r.pcgG),
                    List([1..r.n], k -> im[k]*c[k]));
      if hom = fail or not IsBijective(hom) then return fail; fi;
      return hom;
   end;

   ## r.lift(map,n1,n2,K): the same for an isomorphism map: G/K' --> H/K, where
   ## n1: G --> G/K' and n2: H --> H/K are the natural homomorphisms
   r.lift := function(map, n1, n2, K)
      return r.liftu(List(r.pcgG, x -> Image(map, Image(n1, x))), n2, K);
   end;

   ## r.powtab/r.powcol: the powers of the images that the relations need, computed once
   ## and reused; for a perturbed list of images only one column has to be redone.
   ## r.relvals(im,pw,K,pcgK,wf): the values of the relations of G at im, read in K;
   ## fail if one of them is not in K. If wf is the coordinate vector in K/L for some L
   ## containing [K,H] and K^p, then the wf-part of the equations again has the matrix
   ## r.exp, so the precomputed conditions r.test discard a hopeless im early.
   r.eneed := List([1..r.n], l -> Set(Concatenation(
                 Filtered(List([1..r.nrel], k -> r.exp[k][l]), e -> e > 1), [p])));

   r.powcol := function(x, l)
      local t, e;
      t := [];   t[1] := x;
      for e in r.eneed[l] do t[e] := x^e; od;
      return t;
   end;

   r.powtab := function(im)
      return List([1..r.n], l -> r.powcol(im[l], l));
   end;

   r.relvals := function(im, pw, K, pcgK, wf)
      local out, wv, k, l, v, w, cond;
      out := [];   wv := [];
      for k in [1..r.nrel] do
         if r.rel[k][2] = 0 then
            w := pw[r.rel[k][1]][p];
         else
            w := Comm(im[r.rel[k][2]], im[r.rel[k][1]]);
         fi;
         v := r.oneH;
         for l in r.sup[k] do v := v * pw[l][r.exp[k][l]]; od;
         w := LeftQuotient(v, w);
         if not w in K then return fail; fi;
         if not wf = fail then
            Add(wv, wf(w));
            for cond in r.test[k] do
               if not IsZero(Sum(cond.sup, l -> cond.v[l]*wv[l])) then return fail; fi;
            od;
         fi;
         Add(out, r.one * ExponentsOfPcElement(pcgK, w));
      od;
      return out;
   end;

   ## r.liftmod(map,n1,n2,K,wf): as r.lift, but K only has to be elementary abelian and
   ## NORMAL in H. The conditions on the c_k stay linear over GF(p); their coefficients
   ## involve the action of H on K and are read off by perturbing one image at a time.
   r.liftmod := function(map, n1, n2, K, wf)
      return r.liftmodu(List(r.pcgG,
                x -> PreImagesRepresentative(n2, Image(map, Image(n1, x)))), K, wf);
   end;

   ## r.liftmodu(im,K,wf): as r.liftmod, but for images that are already given in H
   r.liftmodu := function(im, K, wf)
      local pcgK, d, v0, cols, l, t, k, im2, pw, pw2, v, sol, c, hom;
      pcgK := Pcgs(K);
      d    := Length(pcgK);
      pw   := r.powtab(im);
      v0   := r.relvals(im, pw, K, pcgK, wf);
      if v0 = fail then return fail; fi;
      cols := [];
      for l in [1..r.n] do
         for t in [1..d] do
            im2      := ShallowCopy(im);
            im2[l]   := im[l]*pcgK[t];
            pw2      := ShallowCopy(pw);
            pw2[l]   := r.powcol(im2[l], l);
            v        := r.relvals(im2, pw2, K, pcgK, fail);
            if v = fail then return fail; fi;
            Add(cols, Concatenation(List([1..r.nrel], k -> v[k]-v0[k])));
         od;
      od;
      sol := SolutionMat(cols, Concatenation(List(v0, x -> -x)));
      if sol = fail then return fail; fi;
      c   := List([1..r.n], l -> PcElementByExponents(pcgK,
                   List([1..d], t -> IntFFE(sol[(l-1)*d+t]))));
      hom := GroupHomomorphismByImages(G, H, AsList(r.pcgG),
                   List([1..r.n], l -> im[l]*c[l]));
      if hom = fail or not IsBijective(hom) then return fail; fi;
      return hom;
   end;

   ## r.mkwf(K): the coordinate vector in K/(K^p*[K,H]), the largest quotient of K on
   ## which the lifting equations have the image independent matrix r.exp
   r.mkwf := function(K)
      local L, nL, f;
      L  := ClosureGroup(Agemo(K, p), CommutatorSubgroup(K, H));
      if Size(L) = Size(K) then return fail; fi;
      nL := NaturalHomomorphismByNormalSubgroup(K, L);
      f  := Pcgs(Image(nL));
      return w -> r.one*ExponentsOfPcElement(f, Image(nL, w));
   end;

   ## r.relvalsab(im,pw,K,gens,wf): as r.relvals, but read in the abelian group K with
   ## respect to independent generators, so that K may have exponent p^2
   r.relvalsab := function(im, pw, K, gens, wf)
      local out, wv, k, l, v, w, cond;
      out := [];   wv := [];
      for k in [1..r.nrel] do
         if r.rel[k][2] = 0 then
            w := pw[r.rel[k][1]][p];
         else
            w := Comm(im[r.rel[k][2]], im[r.rel[k][1]]);
         fi;
         v := r.oneH;
         for l in r.sup[k] do v := v * pw[l][r.exp[k][l]]; od;
         w := LeftQuotient(v, w);
         if not w in K then return fail; fi;
         if not wf = fail then
            Add(wv, wf(w));
            for cond in r.test[k] do
               if not IsZero(Sum(cond.sup, l -> cond.v[l]*wv[l])) then return fail; fi;
            od;
         fi;
         Add(out, IndependentGeneratorExponents(K, w));
      od;
      return out;
   end;

   ## r.liftab(im,K,wf): lift through a normal ABELIAN kernel K, possibly of exponent
   ## p^2 (for an elementary abelian K, r.liftmodu is faster). The c_l enter through a
   ## homomorphism K^n --> K^nrel, again read off by perturbation; the system is solved
   ## over the integers, with the orders of the generators added as relations.
   r.liftab := function(im, K, wf)
      local gens, ords, rk, pw, v0, cols, l, t, im2, pw2, v, rows, targ, k, j, e, sol,
            c, hom;
      gens := IndependentGeneratorsOfAbelianGroup(K);
      ords := List(gens, Order);
      rk   := Length(gens);
      pw   := r.powtab(im);
      v0   := r.relvalsab(im, pw, K, gens, wf);
      if v0 = fail then return fail; fi;
      cols := [];
      for l in [1..r.n] do
         for t in [1..rk] do
            im2    := ShallowCopy(im);   im2[l] := im[l]*gens[t];
            pw2    := ShallowCopy(pw);   pw2[l] := r.powcol(im2[l], l);
            v      := r.relvalsab(im2, pw2, K, gens, fail);
            if v = fail then return fail; fi;
            Add(cols, Concatenation(List([1..r.nrel], k -> v[k]-v0[k])));
         od;
      od;
      rows := ShallowCopy(cols);
      for k in [1..r.nrel] do
         for j in [1..rk] do
            e := List([1..r.nrel*rk], i -> 0);
            e[(k-1)*rk+j] := ords[j];
            Add(rows, e);
         od;
      od;
      targ := Concatenation(List(v0, x -> -x));
      ## the reduction modulo p of the system is a cheap necessary condition, and the
      ## integer solver below is comparatively expensive
      if SolutionMat(r.one*cols, r.one*targ) = fail then return fail; fi;
      sol := SolutionIntMat(rows, targ);
      if sol = fail then return fail; fi;
      c    := List([1..r.n],
                 l -> Product([1..rk], t -> gens[t]^sol[(l-1)*rk+t]));
      hom  := GroupHomomorphismByImages(G, H, AsList(r.pcgG),
                    List([1..r.n], l -> im[l]*c[l]));
      if hom = fail or not IsBijective(hom) then return fail; fi;
      return hom;
   end;

   ## r.std(gK,KH): the isomorphism G/K --> H/KH from the standard copies of the two
   ## quotients (of order dividing p^4), together with the natural homomorphisms; fail
   ## if the quotients are not isomorphic. r.stdG(K) prepares the source side, which in
   ## (B2) is the same for all p+1 candidates KH.
   r.stdG := function(K)
      local n1;
      n1 := NaturalHomomorphismByNormalSubgroup(G, K);
      return rec(nat := n1, a := p5id_Idp5Group(Image(n1)));
   end;

   r.std := function(gK, KH)
      local n2, b, s;
      if gK.a.iso = fail then return fail; fi;
      n2 := NaturalHomomorphismByNormalSubgroup(H, KH);
      b  := p5id_Idp5Group(Image(n2));
      if b.iso = fail or not gK.a.id = b.id then return fail; fi;
      s  := GroupHomomorphismByImagesNC(Range(gK.a.iso), Range(b.iso),
                Pcgs(Range(gK.a.iso)), Pcgs(Range(b.iso)));
      return rec(map := gK.a.iso*s*InverseGeneralMapping(b.iso), nat := gK.nat,
                 natH := n2, K := KH, Q := Image(n2));
   end;

   ##
   ## (2) the class 2 case: G/C elementary abelian
   ##
   ## r.form(n,K): structure constants wrt Pcgs(Image(n)) and Pcgs(K), that is, B[k] is
   ## the matrix of the k-th coordinate of the commutator map and P[i] the coordinates
   ## of the p-th power of the i-th generator
   r.form := function(n, K)
      local q, f, pz, m, d, li;
      q  := Image(n);   f := Pcgs(q);   pz := Pcgs(K);
      m  := Length(f);  d := Length(pz);
      li := u -> PreImagesRepresentative(n, u);
      return rec( m := m, d := d,
        B := List([1..d], k -> List([1..m], i -> List([1..m], j ->
               r.one*ExponentsOfPcElement(pz, Comm(li(f[i]), li(f[j])))[k]))),
        P := List([1..m], i -> r.one*ExponentsOfPcElement(pz, li(f[i])^p)) );
   end;

   ## r.constr1(dG,dH): dim C = 1, so C --> CH is multiplication by a scalar lam. For
   ## each lam the images of a basis of V are determined one at a time, the conditions
   ## on the next image being linear. The basis is adapted to rad(b) = Z(G)/C, and if b
   ## is nondegenerate and pi nonzero, the image of the first basis vector is fixed.
   r.constr1 := function(dG, dH, tries)
      local RG, RH, xs, fix, s, lam, att, ys, i, j, k, M, tv, sol, ns, y, v, ok;
      RG := NullspaceMat(dG.B[1]);   RH := NullspaceMat(dH.B[1]);
      if not Length(RG) = Length(RH) then return fail; fi;
      s   := Length(RG);
      xs  := ShallowCopy(RG);
      fix := [];
      if s = 0 then
         v := SolutionMat(dG.B[1], List(dG.P, u -> u[1]));
         y := SolutionMat(dH.B[1], List(dH.P, u -> u[1]));
         if not (v = fail or y = fail or IsZero(v) or IsZero(y)) then
            xs := [v];   fix := [y];
         fi;
      fi;
      for v in IdentityMat(dG.m, GF(p)) do
         if RankMat(Concatenation(xs,[v])) > Length(xs) then Add(xs,v); fi;
      od;
      for lam in Filtered(AsList(GF(p)), x -> not IsZero(x)) do
        for att in [1..tries] do
          ys := ShallowCopy(fix);   ok := true;
          for i in [Length(fix)+1..dG.m] do
             M  := [ List(dH.P, v -> v[1]) ];
             tv := [ lam*(xs[i]*List(dG.P, v -> v[1])) ];
             for j in [1..i-1] do
                Add(M, ys[j]*dH.B[1]);
                Add(tv, lam*(xs[j]*dG.B[1]*xs[i]));
             od;
             if i <= s then                      ## x_i is in the radical of b
                for k in [1..dH.m] do
                   Add(M, List([1..dH.m], l -> dH.B[1][l][k]));
                   Add(tv, Zero(GF(p)));
                od;
             fi;
             sol := SolutionMat(TransposedMat(M), tv);
             if sol = fail then ok := false; break; fi;
             ns := NullspaceMat(TransposedMat(M));
             y  := fail;
             for k in [1..30] do
                v := sol;
                for j in [1..Length(ns)] do v := v + Random(GF(p))*ns[j]; od;
                if RankMat(Concatenation(ys,[v])) > Length(ys) and
                   (i <= s or not IsZero(v*dH.B[1])) then
                   y := v;  break;
                fi;
                if ns = [] then break; fi;
             od;
             if y = fail then ok := false; break; fi;
             Add(ys,y);
          od;
          if ok and RankMat(ys) = dG.m then return rec(x := xs, y := ys); fi;
        od;
      od;
      return fail;
   end;

   ## r.plane(dat): here dim V = 3 and dim C = 2, so ker(b) = <om> is 1-dimensional and
   ## om is decomposable; the plane it spans is characteristic (its preimage is the
   ## unique abelian maximal subgroup). Returns the form with that kernel and a basis.
   r.plane := function(dat)
      local ns, om, phi;
      ns := NullspaceMat([ List(dat.B, M -> M[1][2]), List(dat.B, M -> M[1][3]),
                           List(dat.B, M -> M[2][3]) ]);
      if not Length(ns) = 1 then return fail; fi;
      om  := ns[1];
      phi := [ om[3], -om[2], om[1] ];
      return rec(phi := phi, bas := NullspaceMat(TransposedMat([phi])));
   end;

   ## r.constr2(dG,dH): dim V = 3 and dim C = 2. With a basis x1,x2 of the plane and x3
   ## outside it, the map theta on C is determined by the images y1,y2 and the scalar mu
   ## of x3, and the p-power conditions are then linear in y1,y2 and w; so only the p-1
   ## values of mu have to be tried.
   r.constr2 := function(dG, dH)
      local pG, pH, x1, x2, x3, z1, z2, z, cG1, cG2, ab, bz1, bz2, pz1, pz2, pzz,
            i, k, mu, M, tv, e, sol, ns, att, v, y1, y2, w;
      pG := r.plane(dG);   pH := r.plane(dH);
      if pG = fail or pH = fail then return fail; fi;
      x1 := pG.bas[1];  x2 := pG.bas[2];
      x3 := First(IdentityMat(3,GF(p)), v -> not IsZero(pG.phi*v));
      z1 := pH.bas[1];  z2 := pH.bas[2];
      z  := First(IdentityMat(3,GF(p)), v -> not IsZero(pH.phi*v));
      cG1 := List(dG.B, M -> x1*M*x3);
      cG2 := List(dG.B, M -> x2*M*x3);
      if not RankMat([cG1,cG2]) = 2 then return fail; fi;
      ## pi(x_i) = ab[i][1]*cG1 + ab[i][2]*cG2
      ab := List([x1,x2,x3], v -> SolutionMat([cG1,cG2],
                 Sum([1..3], i -> v[i]*dG.P[i])));
      if ForAny(ab, v -> v = fail) then return fail; fi;
      bz1 := List(dH.B, M -> z1*M*z);      ## b'(z1,z)
      bz2 := List(dH.B, M -> z2*M*z);      ## b'(z2,z)
      pz1 := dH.P[1]*z1[1] + dH.P[2]*z1[2] + dH.P[3]*z1[3];   ## pi'(z1)
      pz2 := dH.P[1]*z2[1] + dH.P[2]*z2[2] + dH.P[3]*z2[3];   ## pi'(z2)
      pzz := dH.P[1]*z[1]  + dH.P[2]*z[2]  + dH.P[3]*z[3];    ## pi'(z)
      for mu in Filtered(AsList(GF(p)), x -> not IsZero(x)) do
         ## unknowns: y1 = e1*z1+e2*z2, y2 = e3*z1+e4*z2, w = e5*z1+e6*z2
         M := [];  tv := [];
         for i in [1..3] do
            for k in [1,2] do
               e := [ -mu*ab[i][1]*bz1[k], -mu*ab[i][1]*bz2[k],
                      -mu*ab[i][2]*bz1[k], -mu*ab[i][2]*bz2[k],
                      Zero(GF(p)), Zero(GF(p)) ];
               if i = 1 then
                  e[1] := e[1] + pz1[k];   e[2] := e[2] + pz2[k];
                  Add(tv, Zero(GF(p)));
               elif i = 2 then
                  e[3] := e[3] + pz1[k];   e[4] := e[4] + pz2[k];
                  Add(tv, Zero(GF(p)));
               else
                  e[5] := pz1[k];          e[6] := pz2[k];
                  Add(tv, -mu*pzz[k]);
               fi;
               Add(M, e);
            od;
         od;
         sol := SolutionMat(TransposedMat(M), tv);
         if sol = fail then continue; fi;
         ns := NullspaceMat(TransposedMat(M));
         for att in [1..20] do
            e := sol;
            for v in ns do e := e + Random(GF(p))*v; od;
            y1 := e[1]*z1 + e[2]*z2;
            y2 := e[3]*z1 + e[4]*z2;
            w  := e[5]*z1 + e[6]*z2;
            if RankMat([y1,y2]) = 2 then
               return rec(x := [x1,x2,x3], y := [y1,y2,mu*z+w]);
            fi;
            if ns = [] then break; fi;
         od;
      od;
      return fail;
   end;

   ## r.chars(x): the characteristic subgroups of x that can play the role of C, that is,
   ## the elementary abelian ones inside Z(x) cap Phi(x). A fixed recipe, so entry k for
   ## G and entry k for H correspond to each other.
   r.chars := function(x)
      local b, l, s, u;
      l := LowerCentralSeries(x);
      b := [ FrattiniSubgroup(x), Centre(x), DerivedSubgroup(x), Agemo(x,p),
             l[Length(l)-1], Agemo(Centre(x),p) ];
      return List(Filtered(Combinations([1..Length(b)]), s -> not s = []),
                  function(s)
                     u := Intersection(Concatenation([b[1],b[2]], b{s}));
                     if Size(u) = 1 then return u; fi;
                     return Omega(u,p);
                  end);
   end;


   ## ---------------------------------------------------------------------------
   ## (A) construction: G of class 2 with Phi(G) elementary abelian and central
   ## ---------------------------------------------------------------------------
   r.K := FrattiniSubgroup(G);
   if IsElementaryAbelian(r.K) and IsSubset(Centre(G), r.K) then
      r.KH   := FrattiniSubgroup(H);
      r.natK := NaturalHomomorphismByNormalSubgroup(G, r.K);
      r.natH := NaturalHomomorphismByNormalSubgroup(H, r.KH);
      r.V    := Image(r.natK);
      r.VH   := Image(r.natH);
      r.fG   := r.form(r.natK, r.K);
      r.fH   := r.form(r.natH, r.KH);
      t      := fail;
      if r.fH.d = 1 then
         t := r.constr1(r.fG, r.fH, 10);
      elif r.fH.d = 2 and r.fH.m = 3 then
         t := r.constr2(r.fG, r.fH);
      elif r.fH.m*(r.fH.m-1)/2 + r.fH.m = r.fH.d then
          ## the commutator values and the p-th powers of a basis of V span Phi(G), so
          ## there is no condition: every isomorphism V --> V' is compatible with (b,pi)
         t := rec(x := IdentityMat(r.fG.m, GF(p)), y := IdentityMat(r.fH.m, GF(p)));
      fi;
      if not t = fail then
         r.alp := GroupHomomorphismByImagesNC(r.V, r.VH,
                     List(t.x, v -> PcElementByExponents(Pcgs(r.V),  List(v, IntFFE))),
                     List(t.y, v -> PcElementByExponents(Pcgs(r.VH), List(v, IntFFE))));
         if not r.alp = fail then
            newim := r.lift(r.alp, r.natK, r.natH, r.KH);
            if not newim = fail then
               Info(myp5id, 2, "p5id_iso_random_bruteforce: case A for ",id);
               return newim;
            fi;
         fi;
      fi;
   fi;

   ## ---------------------------------------------------------------------------
   ## (A2) class 3, Phi(G) elementary abelian of order p^2, gamma_3 of order p, rank 3.
   ## With V = G/Phi(G), W = Phi(G)/gamma_3 and C = gamma_3 the commutator maps
   ## V x V --> W and V x W --> C are onto, so an isomorphism is determined by the map
   ## alpha induced on V together with the scalars mu on W and nu on C; alpha must also
   ## match the p-power map and map rad(b) to rad(b'). In the unknowns (alpha,lambda,s,c)
   ## with lambda = nu/mu these conditions are HOMOGENEOUS linear -- rescaling alpha is
   ## not a symmetry, so the scalars must not be normalised away -- and it is enough to
   ## run through the projective points of the solution space, the scalar factor of alpha
   ## being recovered from alpha b' alpha^T = mu*b. Each candidate is lifted (r.liftmod).
   ## ---------------------------------------------------------------------------
   ##
   r.graded := function(X)
      local Ph, g3, nV, V, f, li, nW, W, w0, c0, cw, cc, dat, i, j;
      Ph := FrattiniSubgroup(X);
      g3 := LowerCentralSeries(X)[3];
      nV := NaturalHomomorphismByNormalSubgroup(X, Ph);
      V  := Image(nV);   f := Pcgs(V);
      li := u -> PreImagesRepresentative(nV, u);
      nW := NaturalHomomorphismByNormalSubgroup(Ph, g3);
      W  := Image(nW);
      w0 := PreImagesRepresentative(nW, Pcgs(W)[1]);
      c0 := Pcgs(g3)[1];
      cw := u -> r.one*ExponentsOfPcElement(Pcgs(W), Image(nW,u))[1];
      cc := u -> r.one*ExponentsOfPcElement(Pcgs(g3), u)[1];
      dat := rec(Ph := Ph, g3 := g3, nat := nV, V := V, f := f, w0 := w0, c0 := c0,
                 nW := nW, W := W, m := Length(f));
      dat.b   := List([1..dat.m], i -> List([1..dat.m],
                        j -> cw(Comm(li(f[i]), li(f[j])))));
      dat.phi := List([1..dat.m], i -> cc(Comm(w0, li(f[i]))));
      dat.pi1 := List([1..dat.m], i -> cw(li(f[i])^p));
      if IsZero(dat.pi1) then
         dat.pi2 := List([1..dat.m], i -> cc(li(f[i])^p));
      else
         dat.pi2 := fail;
      fi;
      return dat;
   end;

   ## r.cands(dG,dH): the candidates for alpha, as 3x3 matrices over GF(p); see above
   r.cands := function(dG, dH, lim)
      local res, rG, rH, M, row, k, c, l, ns, d, npts, pts, i, e, v, A,
            s1, s2, w, mu, t, pos, zeropi;
      rG := NullspaceMat(dG.b);   rH := NullspaceMat(dH.b);
      if not (Length(rG) = 1 and Length(rH) = 1) then return []; fi;
      rG := rG[1];   rH := rH[1];
      if not (dG.pi2 = fail) = (dH.pi2 = fail) then return []; fi;
      zeropi := not dG.pi2 = fail and IsZero(dG.pi2);
      if not zeropi = (not dH.pi2 = fail and IsZero(dH.pi2)) then return []; fi;
      ## unknowns: alpha (positions 1..9), lambda (10), s (11), c (12)
      M := [];
      for k in [1..3] do                         ## alpha_k*phi' = lambda*phi_k
         row := List([1..12], c -> Zero(GF(p)));
         for c in [1..3] do row[3*(k-1)+c] := dH.phi[c]; od;
         row[10] := -dG.phi[k];
         Add(M, row);
      od;
      for k in [1..3] do                         ## the p-power condition
         row := List([1..12], c -> Zero(GF(p)));
         if dG.pi2 = fail then
            for c in [1..3] do row[3*(k-1)+c] := dH.pi1[c]; od;
            row[11] := -dG.pi1[k];
         else
            for c in [1..3] do row[3*(k-1)+c] := dH.pi2[c]; od;
            row[11] := -dG.pi2[k];
         fi;
         Add(M, row);
      od;
      if zeropi then                             ## then s is not determined at all
         row := List([1..12], c -> Zero(GF(p)));   row[11] := One(GF(p));   Add(M, row);
      fi;
      for k in [1..3] do                         ## alpha(rad b) = c*rad b'
         row := List([1..12], c -> Zero(GF(p)));
         for l in [1..3] do row[3*(l-1)+k] := rG[l]; od;
         row[12] := -rH[k];
         Add(M, row);
      od;
      ns := NullspaceMat(TransposedMat(M));
      d  := Length(ns);
      if d = 0 then return []; fi;
      ## the projective points of the solution space, or a sample if there are too many
      npts := (p^d-1)/(p-1);   pts := [];   r.full := npts <= lim;
      if r.full then
         for i in [1..d] do
            for e in Tuples(AsList(GF(p)), d-i) do
               v := ShallowCopy(ns[i]);
               for k in [1..d-i] do v := v + e[k]*ns[i+k]; od;
               Add(pts, v);
            od;
         od;
      else
         pts := List([1..lim], i -> Sum(ns, u -> Random(GF(p))*u));
      fi;
      pos := First(Cartesian([1..3],[1..3]), q -> not IsZero(dG.b[q[1]][q[2]]));
      res := [];
      for v in pts do
         A := [v{[1..3]}, v{[4..6]}, v{[7..9]}];
         if IsZero(DeterminantMat(A)) then continue; fi;
         s1 := v[10];   s2 := v[11];
         if IsZero(s1) then continue; fi;
         ## alpha must turn b' into a multiple of b; this also determines mu
         w  := A*dH.b*TransposedMat(A);
         mu := w[pos[1]][pos[2]]/dG.b[pos[1]][pos[2]];
         if IsZero(mu) or not w = mu*dG.b then continue; fi;
         if zeropi then                          ## every scalar multiple works
            Add(res, A);
         elif dG.pi2 = fail then                 ## s = mu fixes the factor
            if IsZero(s2) then continue; fi;
            Add(res, (s2/mu)*A);
         else                                    ## s = nu = lambda*mu fixes it up to a sign
            if IsZero(s2) then continue; fi;
            t := RootFFE(GF(p), s2/(s1*mu), 2);
            if t = fail then continue; fi;
            Add(res, t*A);   Add(res, -t*A);
         fi;
      od;
      Info(myp5id, 3, "p5id_iso_random_bruteforce: (A2) nullity ", d, ", ",
           Length(res), " candidates");
      ## the points are produced in a systematic order, so scan them in random order
      return Permuted(res, Random(SymmetricGroup(Length(res))));
   end;

   if Size(FrattiniSubgroup(G)) = p^2 and IsElementaryAbelian(FrattiniSubgroup(G))
      and NilpotencyClassOfGroup(G) = 3
      and Size(LowerCentralSeries(G)[3]) = p then
      r.dG := r.graded(G);
      r.dH := r.graded(H);
      if r.dG.m = 3 and not IsZero(r.dG.phi) then
         ## the component of Phi(H) modulo [Phi(H),H]; see r.relvals
         r.wf := r.mkwf(r.dH.Ph);
         ## a small sample of candidates first, a large one only if that fails
         r.tryA2 := function(lim)
            local t, alp, new;
            for t in r.cands(r.dG, r.dH, lim) do
               alp := GroupHomomorphismByImagesNC(r.dG.V, r.dH.V, AsList(r.dG.f),
                         List(t, v -> PcElementByExponents(r.dH.f, List(v, IntFFE))));
               if alp = fail then continue; fi;
               new := r.liftmod(alp, r.dG.nat, r.dH.nat, r.dH.Ph, r.wf);
               if not new = fail then return new; fi;
            od;
            return fail;
         end;
         newim := r.tryA2(2000);
         if newim = fail and not r.full then newim := r.tryA2(20000); fi;
         if not newim = fail then
            Info(myp5id, 2, "p5id_iso_random_bruteforce: case A2 for ",id);
            return newim;
         fi;
      fi;
   fi;

   ## ---------------------------------------------------------------------------
   ## (A3) class 2 with |Phi(G)| = p^2 and |G'| = p; then Phi(G) <= Z(G) and rank 3.
   ## The invariants on V = G/Phi(G) are the commutator form b: V x V --> G' (alternating
   ## of rank 2) and the p-power map pi: V --> Phi/G'. An isomorphism scales Phi/G' by mu
   ## and G' by nu, where nu = mu if Phi is cyclic and mu,nu are independent otherwise,
   ## and alpha satisfies b'(alpha x,alpha y) = nu*b(x,y) and pi'(alpha x) = mu*pi(x).
   ## In a basis x,y,z of V with b(x,y) = 1 and z spanning rad(b), such an alpha is built
   ## directly, so candidates arise without rejection. The lift uses r.liftu for an
   ## elementary abelian Phi(H) and r.liftcyc (equations over Z/p^2) for a cyclic one.
   ## ---------------------------------------------------------------------------
   ##
   r.graded2 := function(X)
      local Ph, Xd, nV, V, f, li, u, nU, U, cu, cc, dat, i, j, pos, bas;
      Ph := FrattiniSubgroup(X);
      Xd := DerivedSubgroup(X);
      nV := NaturalHomomorphismByNormalSubgroup(X, Ph);
      V  := Image(nV);   f := Pcgs(V);
      if not Length(f) = 3 then return fail; fi;
      li := u -> PreImagesRepresentative(nV, u);
      u  := First(AsList(Ph), z -> Order(z) = p^2);          ## Phi cyclic
      if u = fail then
         u := First(AsList(Ph), z -> not z in Xd and not IsOne(z));
      fi;
      if u = fail then return fail; fi;
      nU := NaturalHomomorphismByNormalSubgroup(Ph, Xd);       ## Phi --> Phi/G'
      U  := Image(nU);
      cu := z -> r.one*ExponentsOfPcElement(Pcgs(U), Image(nU, z))[1];
      cc := z -> r.one*ExponentsOfPcElement(Pcgs(Xd), z)[1];
      dat := rec(Ph := Ph, nat := nV, V := V, f := f, u := u, m := 3,
                 cyc := Order(u) = p^2);
      ## the coordinates are taken with respect to u mod G' and to a generator of G';
      ## for a cyclic Phi that generator has to be u^p, which is what ties nu to mu
      if dat.cyc then dat.c0 := u^p; else dat.c0 := Pcgs(Xd)[1]; fi;
      dat.b  := List([1..3], i -> List([1..3],
                       j -> cc(Comm(li(f[i]), li(f[j])))/cc(dat.c0)));
      dat.pi := List([1..3], i -> cu(li(f[i])^p)/cu(u));
      if IsZero(dat.pi) then return fail; fi;
       ## for an elementary abelian Phi = <u> x G' the p-power map has a second component
       ## rho in G', a further invariant: rho'(alpha v) = la*pi(v) + nu*rho(v), with one
       ## unknown scalar la
      if dat.cyc then
         dat.rho := fail;
      else
         bas := [ExponentsOfPcElement(Pcgs(Ph), u),
                 ExponentsOfPcElement(Pcgs(Ph), dat.c0)];
         bas := (r.one*bas)^-1;
         dat.rho := List([1..3], i -> ((r.one*ExponentsOfPcElement(Pcgs(Ph),
                            li(f[i])^p))*bas)[2]);
      fi;
      ## a basis x,y,z of V with b(x,y) = 1 and z spanning rad(b)
      if not Length(NullspaceMat(dat.b)) = 1 then return fail; fi;
      dat.z   := NullspaceMat(dat.b)[1];
      pos     := First(Cartesian([1..3],[1..3]), q -> not IsZero(dat.b[q[1]][q[2]]));
      dat.x   := List([1..3], i -> r.one*0);   dat.x[pos[1]] := r.one;
      dat.y   := List([1..3], i -> r.one*0);
      dat.y[pos[2]] := dat.b[pos[1]][pos[2]]^-1;
      dat.P   := [dat.x, dat.y, dat.z];
      if IsZero(DeterminantMat(dat.P)) then return fail; fi;
      dat.Pi  := dat.P^-1;
      return dat;
   end;

   ## r.rsol(rows,vals): a random solution Y of the system Y*rows[j] = vals[j], or fail
   r.rsol := function(rows, vals)
      local mt, sol, w;
      mt  := TransposedMat(rows);
      sol := SolutionMat(mt, vals);
      if sol = fail then return fail; fi;
      for w in NullspaceMat(mt) do sol := sol + Random(GF(p))*w; od;
      return sol;
   end;

   ## r.cand2(dG,dH): a random candidate alpha for (A3), as a 3x3 matrix over GF(p)
   r.units := Filtered(AsList(GF(p)), x -> not IsZero(x));

   r.cand2 := function(dG, dH)
      local mu, nu, la, X, Y, a, s, t, tv, A;
      mu := Random(r.units);
      if dG.cyc then nu := mu; else nu := Random(r.units); fi;
      if dG.rho = fail then
         la := fail;
         a  := r.scal(dH.z*dH.pi, mu*(dG.z*dG.pi));
         if a = fail then return fail; fi;
      else
         ## the two conditions on the image a*z' of z determine a and, with it, la
         s := dH.z*dH.pi;   t := dH.z*dH.rho;
         if not IsZero(dG.z*dG.pi) then
            a := r.scal(s, mu*(dG.z*dG.pi));
            if a = fail then return fail; fi;
            la := (a*t - nu*(dG.z*dG.rho))/(dG.z*dG.pi);
         else
            if not IsZero(s) then return fail; fi;
            la := Random(AsList(GF(p)));
            a  := r.scal(t, nu*(dG.z*dG.rho));
            if a = fail then return fail; fi;
         fi;
      fi;
      if IsZero(a) then return fail; fi;
      if la = fail then
         X := r.rsol([dH.pi], [mu*(dG.x*dG.pi)]);
         if X = fail then return fail; fi;
         Y := r.rsol([dH.pi, X*dH.b], [mu*(dG.y*dG.pi), nu]);
      else
         X := r.rsol([dH.pi, dH.rho],
                 [mu*(dG.x*dG.pi), la*(dG.x*dG.pi) + nu*(dG.x*dG.rho)]);
         if X = fail then return fail; fi;
         Y := r.rsol([dH.pi, dH.rho, X*dH.b],
                 [mu*(dG.y*dG.pi), la*(dG.y*dG.pi) + nu*(dG.y*dG.rho), nu]);
      fi;
      if Y = fail then return fail; fi;
      A := dG.Pi*[X, Y, a*dH.z];
      if IsZero(DeterminantMat(A)) then return fail; fi;
      return A;
   end;

   ## r.scal(s,t): a solution a of a*s = t, a random nonzero one if s and t vanish
   r.scal := function(s, t)
      if not IsZero(s) then return t/s; fi;
      if not IsZero(t) then return fail; fi;
      return Random(r.units);
   end;

   ## r.mkdlog(u): the discrete logarithm table of the cyclic group <u> of order p^2
   r.mkdlog := function(u)
      local D, i;
      D := NewDictionary(r.oneH, true);
      for i in [0..p^2-1] do AddDictionary(D, u^i, i); od;
      return D;
   end;

   ## r.cycprep(): the parts of the equations over Z/p^2 that do not depend on the
   ## images, namely the kernel of the system modulo p and its effect on the residual
   r.cycprep := function()
      local kb, dl, k, l, num, del;
      r.ker := NullspaceMat(r.mat);
      r.del := [];
      for kb in r.ker do
         dl  := List(kb, IntFFE);
         del := [];
         for k in [1..r.nrel] do
            num := -Sum([1..r.n], l -> r.exp[k][l]*dl[l]);
            if r.rel[k][2] = 0 then num := num + p*dl[r.rel[k][1]]; fi;
            Add(del, num/p);
         od;
         Add(r.del, del);
      od;
      r.amat := List(r.del,
                   del -> List(r.left,
                      t -> Sum([1..r.nrel], k -> t[k]*(r.one*del[k]))));
   end;

   ## r.cycres(om,ga): the residual (om - E*ga)/p of the system modulo p^2, or fail
   r.cycres := function(om, ga)
      local out, k, l, num;
      out := [];
      for k in [1..r.nrel] do
         num := om[k] - Sum([1..r.n], l -> r.exp[k][l]*ga[l]);
         if r.rel[k][2] = 0 then num := num + p*ga[r.rel[k][1]]; fi;
         if not num mod p = 0 then return fail; fi;
         Add(out, num/p);
      od;
      return out;
   end;

   ## r.liftcyc(im,u): lift through the central cyclic kernel <u> of order p^2. With the
   ## corrections written as u^gamma the relations read sum_l exp[k][l]*gamma_l -
   ## p*gamma_i = omega_k mod p^2 (the second term only for the power relation of i).
   ## Modulo p this is the system of r.liftu, so r.test applies; the solution is then
   ## corrected inside its kernel so that the second order part becomes solvable too.
   r.liftcyc := function(im, u)
      local om, k, l, w, v, cond, ga, rho, s, i, g1, c, hom;
      if not IsBound(r.amat) then r.cycprep(); fi;
      om := [];
      for k in [1..r.nrel] do
         if r.rel[k][2] = 0 then
            w := im[r.rel[k][1]]^p;
         else
            w := Comm(im[r.rel[k][2]], im[r.rel[k][1]]);
         fi;
         v := r.oneH;
         for l in r.sup[k] do v := v * im[l]^r.exp[k][l]; od;
         w := LookupDictionary(r.dlog, LeftQuotient(v, w));
         if w = fail then return fail; fi;
         Add(om, w);
         for cond in r.test[k] do
            if not IsZero(Sum(cond.sup, l -> cond.v[l]*(r.one*om[l]))) then
               return fail;
            fi;
         od;
      od;
      ga := SolutionMat(r.mat, r.one*om);
      if ga = fail then return fail; fi;
      ga  := List(ga, IntFFE);
      rho := r.cycres(om, ga);
      if rho = fail then return fail; fi;
      s := SolutionMat(r.amat,
              List(r.left, t -> -Sum([1..r.nrel], k -> t[k]*(r.one*rho[k]))));
      if s = fail then return fail; fi;
      for i in [1..Length(r.ker)] do
         ga := ga + IntFFE(s[i])*List(r.ker[i], IntFFE);
      od;
      rho := r.cycres(om, ga);
      if rho = fail then return fail; fi;
      g1 := SolutionMat(r.mat, r.one*rho);
      if g1 = fail then return fail; fi;
      c   := List([1..r.n], l -> u^((ga[l] + p*IntFFE(g1[l])) mod p^2));
      hom := GroupHomomorphismByImages(G, H, AsList(r.pcgG),
                   List([1..r.n], l -> im[l]*c[l]));
      if hom = fail or not IsBijective(hom) then return fail; fi;
      return hom;
   end;

   if NilpotencyClassOfGroup(G) = 2 and Size(FrattiniSubgroup(G)) = p^2
      and Size(DerivedSubgroup(G)) = p then
      r.dG2 := r.graded2(G);
      r.dH2 := r.graded2(H);
      if not (r.dG2 = fail or r.dH2 = fail) and r.dG2.cyc = r.dH2.cyc then
         if r.dH2.cyc then r.dlog := r.mkdlog(r.dH2.u); fi;
         ## the coordinates of the generators of G in V
         r.cG := List(r.pcgG, x -> r.one*ExponentsOfPcElement(r.dG2.f,
                         Image(r.dG2.nat, x)));
         r.tryA3 := function(tot)
            local i, A, im, new;
            for i in [1..tot] do
               ## a draw of the scalars can be inconsistent; that discards this
               ## candidate only, not the whole case
               A := r.cand2(r.dG2, r.dH2);
               if A = fail then continue; fi;
               im := List(r.cG, v -> PcElementByExponents(r.dH2.f,
                             List(v*A, IntFFE)));
               if r.dH2.cyc then
                  new := r.liftcyc(List(im, y -> PreImagesRepresentative(r.dH2.nat, y)),
                            r.dH2.u);
               else
                  new := r.liftu(im, r.dH2.nat, r.dH2.Ph);
               fi;
               if not new = fail then return new; fi;
            od;
            return fail;
         end;
         newim := r.tryA3(20000);
         if not newim = fail then
            Info(myp5id, 2, "p5id_iso_random_bruteforce: case A3 for ",id);
            return newim;
         fi;
      fi;
   fi;

   ## ---------------------------------------------------------------------------
   ## (A4) two generator groups with Phi(G) = G' elementary abelian of order p^3. Then
   ## V = G/Phi(G) has dimension 2 and Phi/gamma_3 is canonically the exterior square of
   ## V, so with the generator w0 = [e1,e2] an isomorphism acts on it by det(alpha).
   ## Everything else is measured against w0: with t0 = [w0,e_j] and s0 = [t0,e_k] the
   ## scalars on gamma_3/gamma_4 and gamma_4 are tau = det(alpha)*q2'(alpha e_j) and
   ## sigma = tau*q3'(alpha e_k), where q2,q3 are the forms v -> [w0,v] and v -> [t0,v];
   ## the p-power map is matched layer by layer with the corresponding scalar. For class
   ## 4 this leaves a handful of candidates. For class 3 the graded Lie ring is free, so
   ## the brackets give no condition, but gamma_3 is then canonically V and the p-power
   ## map becomes an endomorphism Theta of V with Theta'*alpha = det(alpha)*alpha*Theta,
   ## which again leaves about p candidates. Each is lifted with kernel Phi(H).
   ## ---------------------------------------------------------------------------
   ##
   r.graded4 := function(X)
      local Ph, lc, cl, nV, V, f, li, g3, g4, nW, W, w, cw, n3, c3, c4, t, dat, i, j,
            bas, co;
      Ph := FrattiniSubgroup(X);   lc := LowerCentralSeries(X);
      cl := Length(lc)-1;
      if not cl in [3,4] then return fail; fi;
      nV := NaturalHomomorphismByNormalSubgroup(X, Ph);
      V  := Image(nV);   f := Pcgs(V);
      if not Length(f) = 2 then return fail; fi;
      li := u -> PreImagesRepresentative(nV, u);
      g3 := lc[3];
      nW := NaturalHomomorphismByNormalSubgroup(Ph, g3);
      W  := Image(nW);
      w  := Comm(li(f[1]), li(f[2]));            ## the canonical generator of Phi/gamma_3
      if Image(nW, w) = One(W) then return fail; fi;
      cw := z -> r.one*ExponentsOfPcElement(Pcgs(W), Image(nW, z))[1]
                  /(r.one*ExponentsOfPcElement(Pcgs(W), Image(nW, w))[1]);
      dat := rec(Ph := Ph, nat := nV, V := V, f := f, cl := cl, w0 := w);
      dat.q1 := List([1..2], i -> cw(li(f[i])^p));       ## p-power map modulo gamma_3
      if cl = 3 then
         ## gamma_3 is identified with V by v -> [w0,v]
         dat.F := List([1..2], i -> r.one*ExponentsOfPcElement(Pcgs(g3),
                            Comm(w, li(f[i]))));
         if IsZero(DeterminantMat(dat.F)) then return fail; fi;
         dat.Pw := List([1..2], i -> r.one*ExponentsOfPcElement(Pcgs(g3),
                            li(f[i])^p));
         dat.Th := dat.Pw*dat.F^-1;
         return dat;
      fi;
      ## class 4
      g4 := lc[4];
      n3 := NaturalHomomorphismByNormalSubgroup(g3, g4);
      c3 := z -> r.one*ExponentsOfPcElement(Pcgs(Image(n3)), Image(n3, z))[1];
      dat.j := First([1..2], i -> not Comm(w, li(f[i])) in g4);
      if dat.j = fail then return fail; fi;
      t  := Comm(w, li(f[dat.j]));                       ## the generator t0 of gamma_3/gamma_4
      dat.q2 := List([1..2], i -> c3(Comm(w, li(f[i])))/c3(t));
      dat.k  := First([1..2], i -> not IsOne(Comm(t, li(f[i]))));
      if dat.k = fail then return fail; fi;
      c4 := z -> r.one*ExponentsOfPcElement(Pcgs(g4), z)[1]
                  /(r.one*ExponentsOfPcElement(Pcgs(g4), Comm(t, li(f[dat.k])))[1]);
      dat.q3 := List([1..2], i -> c4(Comm(t, li(f[i]))));
      ## w0, t0 and s0 are a basis of the elementary abelian group Phi, so the p-power
      ## map can be read off in all three layers at once
      bas := (r.one*[ExponentsOfPcElement(Pcgs(Ph), w),
                     ExponentsOfPcElement(Pcgs(Ph), t),
                     ExponentsOfPcElement(Pcgs(Ph), Comm(t, li(f[dat.k])))])^-1;
      if bas = fail then return fail; fi;
      co := List([1..2],
               i -> (r.one*ExponentsOfPcElement(Pcgs(Ph), li(f[i])^p))*bas);
      dat.q1 := List(co, v -> v[1]);
      dat.q4 := List(co, v -> v[2]);
      dat.q5 := List(co, v -> v[3]);
      ## for v with q2(v) = q3(v) = 0 the commutator [w0,v] lies in gamma_4 already, and
      ## its value there is one more invariant: det(alpha)*lam'(alpha v) = sigma*lam(v)
      dat.lam := function(v)
         return c4(Comm(w, li(PcElementByExponents(f, List(v, IntFFE)))));
      end;
      return dat;
   end;

   ## r.spanres(v,sp): residuals that vanish exactly if the vector v lies in the span
   ## of the list sp; they are linear in v
   r.spanres := function(v, sp)
      if sp = [] then return v; fi;
      if Length(sp) = 1 then
         return [v[1]*sp[1][2] - v[2]*sp[1][1]];
      fi;
      if RankMat(sp) >= 2 then return []; fi;
      return [v[1]*sp[1][2] - v[2]*sp[1][1]];
   end;

   ## r.res4(A,dG,dH): residuals of the conditions of (A4) for a class 4 candidate. The
   ## p-power map is matched layer by layer, in each layer only up to the span of the
   ## forms of the previous layers, which is the freedom of the unknown deeper parts.
   r.res4 := function(A, dG, dH)
      local dt, tau, sig, out, sp, sc;
      dt  := DeterminantMat(A);
      tau := dt*(A[dG.j]*dH.q2);
      sig := tau*(A[dG.k]*dH.q3);
      out := ShallowCopy(A*dH.q2 - (A[dG.j]*dH.q2)*dG.q2);
      Append(out, A*dH.q3 - (A[dG.k]*dH.q3)*dG.q3);
      sp  := [];
      if not (IsZero(dG.q1) and IsZero(dH.q1)) then
         Append(out, A*dH.q1 - dt*dG.q1);
         Add(sp, dG.q1);
      fi;
      if not (IsZero(dG.q4) and IsZero(dH.q4)) then
         Append(out, r.spanres(A*dH.q4 - tau*dG.q4, sp));
         Add(sp, dG.q4);
      fi;
      if not (IsZero(dG.q5) and IsZero(dH.q5)) then
         Append(out, r.spanres(A*dH.q5 - sig*dG.q5, sp));
      fi;
      ## the second order commutator form on the canonical line
      if not (r.lG4 = fail or r.lH4 = fail) then
         sc := (r.u1G4*A)[r.c4]/r.u1H4[r.c4];
         Add(out, dt*sc*r.lH4 - sig*r.lG4);
      fi;
      return out;
   end;

   ## r.solveq(f0,f1,f2): the set of x in GF(p) with F(x) = 0, where F is a vector of
   ## polynomials of degree at most 2 given by its values at 0, 1 and 2
   r.solveq := function(f0, f1, f2)
      local all, res, k, c0, c1, c2, di, w;
      all := AsList(GF(p));   res := fail;
      for k in [1..Length(f0)] do
         c0 := f0[k];
         c2 := (f2[k] - 2*f1[k] + c0)/(r.one*2);
         c1 := f1[k] - c0 - c2;
         if IsZero(c2) and IsZero(c1) then
            if not IsZero(c0) then return []; fi;
            continue;
         elif IsZero(c2) then
            w := [-c0/c1];
         else
            di := c1^2 - 4*c2*c0;
            if IsZero(di) then
               w := [-c1/(2*c2)];
            else
               di := RootFFE(GF(p), di, 2);
               if di = fail then return []; fi;
               w := [(-c1+di)/(2*c2), (-c1-di)/(2*c2)];
            fi;
         fi;
         if res = fail then res := w; else res := Filtered(res, x -> x in w); fi;
         if res = [] then return []; fi;
      od;
      if res = fail then return all; fi;
      return res;
   end;

   ## r.cands4(dG,dH): the candidates for alpha in (A4), or fail if there are too many
   r.cands4 := function(dG, dH)
      local res, cap, ker, u1G, u2G, u1H, u2H, PG, PH, s, t, A, d, ns, i, j,
            e, u, v, c, dt, M, row, pts;
      cap := 300000;   res := [];
      if not dG.cl = dH.cl then return []; fi;
      if dG.cl = 3 then
         ## the intertwining condition alpha*Theta' = det(alpha)*Theta*alpha, written as
         ## a homogeneous system in the four entries of alpha for each value of det
         for d in r.units do
            M := [];
            for i in [1..2] do
               for j in [1..2] do                      ## the unknown alpha[i][j]
                  row := [];
                  for t in [1..2] do
                     for u in [1..2] do                ## the equation in position (t,u)
                        c := Zero(GF(p));
                        if i = t then c := c + dH.Th[j][u]; fi;
                        if j = u then c := c - d*dG.Th[t][i]; fi;
                        Add(row, c);
                     od;
                  od;
                  Add(M, row);
               od;
            od;
            ns := NullspaceMat(M);
            if ns = [] then continue; fi;
            ## det(alpha) = d fixes the scalar factor, so the projective points of the
            ## space of intertwiners suffice; a sample if that space is large
            pts := [];
            if Length(ns) <= 2 then
               for i in [1..Length(ns)] do
                  for e in Tuples(AsList(GF(p)), Length(ns)-i) do
                     v := ShallowCopy(ns[i]);
                     for t in [1..Length(ns)-i] do v := v + e[t]*ns[i+t]; od;
                     Add(pts, v);
                  od;
               od;
            else
               for i in [1..100] do
                  v := ns[1]*Zero(GF(p));
                  for t in [1..Length(ns)] do v := v + Random(GF(p))*ns[t]; od;
                  Add(pts, v);
               od;
            fi;
            for v in pts do
               A  := [v{[1,2]}, v{[3,4]}];
               dt := DeterminantMat(A);
               if IsZero(dt) then continue; fi;
               c := RootFFE(GF(p), d/dt, 2);
               if c = fail then continue; fi;
               A := c*A;
               if not IsZero(dG.q1) and not A*dH.q1 = d*dG.q1 then continue; fi;
               Add(res, A);   Add(res, -A);
               if Length(res) > cap then return fail; fi;
            od;
         od;
         return Permuted(res, Random(SymmetricGroup(Length(res))));
      fi;
      return [];            ## class 4 is handled by r.mats4, one pair (s,t) at a time
   end;

   ## r.base4(dG,dH): the bases adapted to the kernels of q2 and q2'
   r.base4 := function(dG, dH)
      local ker, u1G, u1H, u2G, u2H;
      ker := q -> [q[2], -q[1]];
      u1G := ker(dG.q2);   u1H := ker(dH.q2);
      u2G := First([[r.one, r.one*0], [r.one*0, r.one]],
                v -> not IsZero(u1G[1]*v[2]-u1G[2]*v[1]));
      u2H := First([[r.one, r.one*0], [r.one*0, r.one]],
                v -> not IsZero(u1H[1]*v[2]-u1H[2]*v[1]));
      return rec(PG := [u1G, u2G]^-1, PH := [u1H, u2H]);
   end;

   ## r.mats4(s,t,dG,dH): the class 4 candidates alpha = [[s,0],[a,t]] in the adapted
   ## basis; for fixed s,t the conditions have degree at most 2 in a, so a is solved for
   r.mats4 := function(s, t, dG, dH)
      local mat, A, c;
      mat := c -> r.bs4.PG*[[s, Zero(GF(p))], [c, t]]*r.bs4.PH;
      A   := List([0,1,2], c -> r.res4(mat(r.one*c), dG, dH));
      return List(r.solveq(A[1], A[2], A[3]), c -> mat(c));
   end;

   if Size(FrattiniSubgroup(G)) = p^3 and IsElementaryAbelian(FrattiniSubgroup(G))
      and FrattiniSubgroup(G) = DerivedSubgroup(G) then
      r.dG4 := r.graded4(G);
      r.dH4 := r.graded4(H);
      if not (r.dG4 = fail or r.dH4 = fail) then
         r.PhH := FrattiniSubgroup(H);
         r.wf2 := r.mkwf(r.PhH);
         r.fH4 := Pcgs(r.dH4.V);
         r.cG  := List(r.pcgG, x -> r.one*ExponentsOfPcElement(r.dG4.f,
                          Image(r.dG4.nat, x)));
         r.tryA4 := function()
            local cd, t, im, new, pairs, q, A;
            ## only a fraction of the candidates lifts, so they are tried in random
            ## order and produced only as far as they are needed
            if r.dG4.cl = 3 then
               cd := r.cands4(r.dG4, r.dH4);
               if cd = fail then return fail; fi;
               Info(myp5id, 3, "p5id_iso_random_bruteforce: (A4) ",
                    Length(cd), " candidates");
            else
               r.bs4 := r.base4(r.dG4, r.dH4);
               ## the canonical line and the second order commutator form on it; the
               ## form is only canonical when the kernels of q2 and q3 agree
               r.lG4 := fail;   r.lH4 := fail;
               r.u1G4 := (r.bs4.PG^-1)[1];   r.u1H4 := r.bs4.PH[1];
               r.c4   := First([1..2], i -> not IsZero(r.u1H4[i]));
               if IsZero(r.dG4.q2[1]*r.dG4.q3[2]-r.dG4.q2[2]*r.dG4.q3[1]) then
                  r.lG4 := r.dG4.lam(r.u1G4);
                  r.lH4 := r.dH4.lam(r.u1H4);
                  if IsZero(r.lG4) and IsZero(r.lH4) then
                     r.lG4 := fail;   r.lH4 := fail;
                  fi;
               fi;
               cd    := fail;
            fi;
            if cd = fail then
               ## the pairs (s,t) are taken in random order, but the candidates of a
               ## batch are mixed before they are tried: the ones that lift sit in few pairs
               pairs := Cartesian(r.units, r.units);
               pairs := Permuted(pairs, Random(SymmetricGroup(Length(pairs))));
            else
               pairs := [];
            fi;
            A := cd;
            for q in [1..Length(pairs)+1] do
               if q <= Length(pairs) then
                  if A = fail then A := []; fi;
                  Append(A, r.mats4(pairs[q][1], pairs[q][2], r.dG4, r.dH4));
                  if Length(A) < 3000 and q < Length(pairs) then continue; fi;
               elif A = fail then
                  return fail;
               fi;
               for t in Permuted(A, Random(SymmetricGroup(Length(A)))) do
                  im := List(r.cG, v -> PreImagesRepresentative(r.dH4.nat,
                                PcElementByExponents(r.fH4, List(v*t, IntFFE))));
                  new := r.liftmodu(im, r.PhH, r.wf2);
                  if not new = fail then return new; fi;
               od;
               A := [];
               if q > Length(pairs) then return fail; fi;
            od;
            return fail;
         end;
         newim := r.tryA4();
         if not newim = fail then
            Info(myp5id, 2, "p5id_iso_random_bruteforce: case A4 for ",id);
            return newim;
         fi;
      fi;
   fi;

   ## ---------------------------------------------------------------------------
   ## (A5) the remaining two generator groups, where Phi(G) is not elementary abelian or
   ## is larger than G'. With D = Phi^p*[Phi,G] and U = Phi/D both the p-power map
   ## pi: V --> U and the commutator b = [e1,e2] in U are canonical, and an isomorphism
   ## induces beta on U with beta*pi = pi'*alpha and beta(b) = det(alpha)*b'. Hence alpha
   ## maps ker(pi) to ker(pi'), and if pi is injective with b = pi(v0), then
   ## alpha(v0) = det(alpha)*v0'. Deeper conditions come from D (r.res5). The candidates
   ## are lifted through Phi(H), which may have exponent p^2 (r.liftab); modulo D the
   ## equations again have the matrix r.exp, so r.test rejects most of them at once.
   ## ---------------------------------------------------------------------------
   ##
   r.graded5 := function(X)
      local Ph, D, nU, U, fu, nV, V, fv, li, dat, i, j, D2, nL, L,
            nA, A, U1, U2, U3, n1, n2, x, g1, g2, c1, c2, cb;
      Ph := FrattiniSubgroup(X);
      nV := NaturalHomomorphismByNormalSubgroup(X, Ph);
      V  := Image(nV);   fv := Pcgs(V);
      if not Length(fv) = 2 then return fail; fi;
      li := u -> PreImagesRepresentative(nV, u);
      D  := ClosureGroup(Agemo(Ph, p), CommutatorSubgroup(Ph, X));
      nU := NaturalHomomorphismByNormalSubgroup(Ph, D);
      U  := Image(nU);   fu := Pcgs(U);
      dat := rec(Ph := Ph, nat := nV, V := V, f := fv, D := D, U := U, m := Length(fu),
                 li := li, expp := Exponent(Ph) = p);
      dat.pi := List([1..2], i -> r.one*ExponentsOfPcElement(fu,
                          Image(nU, li(fv[i])^p)));
      dat.b  := r.one*ExponentsOfPcElement(fu, Image(nU, Comm(li(fv[1]), li(fv[2]))));
      if dat.m = 0 then dat.rk := 0; else dat.rk := RankMat(dat.pi); fi;
      ## v0 with pi(v0) = b, if b lies in the image of an injective pi
      dat.v0 := fail;
      if dat.rk = 2 then dat.v0 := SolutionMat(dat.pi, dat.b); fi;
      ## for class 2 the p-power map is a homomorphism, so X/X' has a canonical filtration
      ## by p-th powers; if its layers are 1-dimensional, then the forms tau_k(v) =
      ## v^(p^k) are canonical and, with generators chosen as p-th powers of each other,
      ## an isomorphism scales all of them by the SAME scalar m
      dat.tau := fail;
      if NilpotencyClassOfGroup(X) = 2 then
         nA := NaturalHomomorphismByNormalSubgroup(X, DerivedSubgroup(X));
         A  := Image(nA);
         U1 := Agemo(A, p, 1);   U2 := Agemo(A, p, 2);   U3 := Agemo(A, p, 3);
         if Size(U1)/Size(U2) = p and Size(U2)/Size(U3) = p then
            n1 := NaturalHomomorphismByNormalSubgroup(U1, U2);
            n2 := NaturalHomomorphismByNormalSubgroup(U2, U3);
            x  := First(List(fv, u -> Image(nA, li(u))),
                     y -> not y^p in U2 and not y^(p^2) in U3);
            if not x = fail then
               g1 := Image(n1, x^p);   g2 := Image(n2, x^(p^2));
               c1 := z -> r.one*ExponentsOfPcElement(Pcgs(Image(n1)), Image(n1, z))[1]
                           /(r.one*ExponentsOfPcElement(Pcgs(Image(n1)), g1)[1]);
               c2 := z -> r.one*ExponentsOfPcElement(Pcgs(Image(n2)), Image(n2, z))[1]
                           /(r.one*ExponentsOfPcElement(Pcgs(Image(n2)), g2)[1]);
               dat.tau := [List(fv, u -> c1(Image(nA, li(u))^p)),
                           List(fv, u -> c2(Image(nA, li(u))^(p^2)))];
            fi;
         fi;
      fi;
      ## the next layer: the canonical pairing mu: U x V --> D/(D^p*[D,X]), which is
      ## well defined because Phi is abelian. It is used through r.ok5.
      D2 := ClosureGroup(Agemo(D, p), CommutatorSubgroup(D, X));
      nL := NaturalHomomorphismByNormalSubgroup(D, D2);
      L  := Image(nL);
      dat.nL := nL;   dat.L := L;
      ## the p-power map on the kernel of pi, which lands in D when Phi has exponent p
      dat.kap := fail;
      if dat.expp and Length(Pcgs(L)) = 1 then
         dat.kap := function(v)
            local z;
            z := li(PcElementByExponents(fv, List(v, IntFFE)))^p;
            if not z in D then return fail; fi;
            return r.one*ExponentsOfPcElement(Pcgs(L), Image(nL, z))[1];
         end;
      fi;
      dat.mu  := fail;
      dat.rho := fail;
      if Length(Pcgs(L)) = 1 and dat.m > 0 then
         dat.mu := List([1..dat.m], i -> List([1..2],
            j -> r.one*ExponentsOfPcElement(Pcgs(L), Image(nL,
                    Comm(PreImagesRepresentative(nU, fu[i]), li(fv[j]))))[1]));
         if IsZero(dat.mu) then dat.mu := fail; fi;
         ## if D has exponent p, then u -> u^p is a well defined map U --> D/D2, with
         ## the same scalar as the pairing; that is one more condition
         if Exponent(D) = p then
            dat.rho := List([1..dat.m],
               i -> r.one*ExponentsOfPcElement(Pcgs(L), Image(nL,
                       PreImagesRepresentative(nU, fu[i])^p))[1]);
            if IsZero(dat.rho) then dat.rho := fail; fi;
         fi;
      fi;
      ## the second p-power layer as a form on V: y(v) = v^(p^2) in D/D2; if the
      ## commutator lies in D, then the scalar there is det(alpha)
      dat.y := fail;
      if not dat.rho = fail then
         dat.y := dat.pi*dat.rho;
         if IsZero(dat.y) then dat.y := fail; fi;
      fi;
      dat.b0 := dat.m > 0 and IsZero(dat.b)
                  and not IsOne(Comm(li(fv[1]), li(fv[2])));
      if dat.b0 then
         ## then the commutator itself lies in D, and it is the right unit for the
         ## coordinates there: with respect to it the scalar of the layer is det(alpha)
         cb := r.one*ExponentsOfPcElement(Pcgs(L),
                  Image(nL, Comm(li(fv[1]), li(fv[2]))))[1];
         if IsZero(cb) then
            dat.b0 := false;
         else
            if not dat.rho = fail then dat.rho := dat.rho/cb; fi;
            if not dat.y   = fail then dat.y   := dat.y/cb;   fi;
         fi;
      fi;
      return dat;
   end;

   ## r.base5(dG,dH): bases of V and V' adapted to the canonical line of each side, and
   ## the shape of the candidates: "line", "vec" or "free" (no condition from this layer)
   r.base5 := function(dG, dH)
      local cmpl, mk, ker, u1G, u1H;
      cmpl := u -> First([[r.one, r.one*0], [r.one*0, r.one]],
                      v -> not IsZero(u[1]*v[2]-u[2]*v[1]));
      mk := function(kind, uG, uH)
         local PG, PH;
         if uG = fail or uH = fail or IsZero(uG) or IsZero(uH) then return fail; fi;
         PG := [uG, cmpl(uG)];   PH := [uH, cmpl(uH)];
         if IsZero(DeterminantMat(PG)) or IsZero(DeterminantMat(PH)) then
            return fail;
         fi;
         return rec(kind := kind, PG := PG^-1, PH := PH,
                    dd := DeterminantMat(PH)/DeterminantMat(PG));
      end;
      if not dG.rk = dH.rk then return fail; fi;
      ## the kernel of the p-power map, if it is a line
      if dG.rk = 1 and dG.m > 0 and dH.m > 0 then
         ker := d -> NullspaceMat(d.pi);
         if Length(ker(dG)) = 1 and Length(ker(dH)) = 1 then
            u1G := mk("line", ker(dG)[1], ker(dH)[1]);
            if not u1G = fail then return u1G; fi;
         fi;
      fi;
      ## if pi is injective and b lies in its image, then alpha(v0) = det(alpha)*v0'
      if dG.rk = 2 and not (dG.v0 = fail or dH.v0 = fail) then
         u1G := mk("vec", dG.v0, dH.v0);
         if not u1G = fail then return u1G; fi;
      fi;
      ## the kernel of the second p-power form, if there is one
      if not (dG.y = fail or dH.y = fail) then
         u1G := mk("line", [dG.y[2], -dG.y[1]], [dH.y[2], -dH.y[1]]);
         if not u1G = fail then return u1G; fi;
      fi;
      ## otherwise the right kernel of the canonical pairing, if it is a line
      if not (dG.mu = fail or dH.mu = fail) then
         ker := d -> NullspaceMat(TransposedMat(d.mu));
         if Length(ker(dG)) = 1 and Length(ker(dH)) = 1 then
            u1G := mk("line", ker(dG)[1], ker(dH)[1]);
            if not u1G = fail then return u1G; fi;
         fi;
      fi;
      return rec(kind := "free");
   end;

   ## r.tcands(dG,dH): the candidates from the p-power layers of (A5); the conditions
   ## are homogeneous in (alpha,m), so every nonzero solution is taken
   r.tcands := function(dG, dH)
      local M, k, j, c, row, ns, d, v, t, A, res;
      M := [];
      for k in [1..Length(dG.tau)] do
         for j in [1..2] do
            row := List([1..5], c -> Zero(GF(p)));
            for c in [1..2] do row[2*(j-1)+c] := dH.tau[k][c]; od;
            row[5] := -dG.tau[k][j];
            Add(M, row);
         od;
      od;
      ns := NullspaceMat(TransposedMat(M));
      d  := Length(ns);
      ## the solution space is taken as a whole (its scalar multiples are different
      ## candidates); if it is too large, then the conditions are too weak to be useful
      if d = 0 or (p^d-1) > 12000 then return fail; fi;
      res := [];
      for t in Tuples(AsList(GF(p)), d) do
         v := ns[1]*Zero(GF(p));
         for k in [1..d] do v := v + t[k]*ns[k]; od;
         if IsZero(v[5]) then continue; fi;
         A := [v{[1,2]}, v{[3,4]}];
         if not IsZero(DeterminantMat(A)) then Add(res, A); fi;
      od;
      return res;
   end;

   ## r.linv(T,m): a left inverse of the 3 x m matrix T of rank m, or fail
   r.linv := function(T, m)
      local I, si, Tl, i, k;
      I := First(Combinations([1..3], m), c -> RankMat(T{c}) = m);
      if I = fail then return fail; fi;
      si := (T{I})^-1;
      Tl := List([1..m], i -> List([1..3], k -> Zero(GF(p))));
      for i in [1..m] do
         for k in [1..m] do Tl[i][I[k]] := si[i][k]; od;
      od;
      return Tl;
   end;

   ## r.res5(A,dG,dH): residuals of the conditions from the layer D/D2. Here beta is
   ## determined by beta*pi = pi'*alpha and beta(b) = det(alpha)*b', and the pairing with
   ## V, the p-power map on U, the form y and the p-power map on the canonical line must
   ## all be preserved with ONE common scalar, read off from the pairing or equal to
   ## det(alpha). All residuals have degree at most 2 in each entry of A.
   r.res5 := function(A, dG, dH)
      local T, S, be, w, v, sc, cnum, cden, out, i, j;
      if r.Tl5 = fail then return []; fi;
      T   := Concatenation(dG.pi, [dG.b]);
      S   := Concatenation(A*dH.pi, [DeterminantMat(A)*dH.b]);
      be  := r.Tl5*S;
      out := Concatenation(T*be - S);
      cnum := fail;   cden := r.one;
      if not (dG.mu = fail or dH.mu = fail) then
         w    := be*dH.mu*TransposedMat(A);
         cnum := w[r.pos5[1]][r.pos5[2]];
         cden := dG.mu[r.pos5[1]][r.pos5[2]];
         for i in [1..dG.m] do
            for j in [1..2] do
               Add(out, w[i][j]*cden - cnum*dG.mu[i][j]);
            od;
         od;
      elif dG.b0 and dH.b0 then
         cnum := DeterminantMat(A);
      fi;
      if cnum = fail then return out; fi;
      if not (dG.rho = fail or dH.rho = fail) then
         v := be*dH.rho;
         for i in [1..dG.m] do Add(out, v[i]*cden - cnum*dG.rho[i]); od;
      fi;
      if not (dG.y = fail or dH.y = fail) then
         v := A*dH.y;
         for j in [1..2] do Add(out, v[j]*cden - cnum*dG.y[j]); od;
      fi;
      if not (r.kG5 = fail or r.kH5 = fail) then
         sc := (r.u1G5*A)[r.c5]/r.u1H5[r.c5];
         Add(out, sc*r.kH5*cden - cnum*r.kG5);
      fi;
      return out;
   end;

   ## r.ok5(A,dG,dH): the same conditions as a test, including that alpha is invertible
   r.ok5 := function(A, dG, dH)
      if IsZero(DeterminantMat(A)) then return false; fi;
      if r.Tl5 = fail then return true; fi;
      return IsZero(r.res5(A, dG, dH));
   end;

   if Size(FrattiniSubgroup(G)) = p^3 and IsAbelian(FrattiniSubgroup(G))
      and not (IsElementaryAbelian(FrattiniSubgroup(G))
               and FrattiniSubgroup(G) = DerivedSubgroup(G)) then
      r.dG5 := r.graded5(G);
      r.dH5 := r.graded5(H);
      r.bs5 := fail;
      if not (r.dG5 = fail or r.dH5 = fail) then r.bs5 := r.base5(r.dG5, r.dH5); fi;
      if not (r.bs5 = fail or r.dG5 = fail or r.dH5 = fail) then
         r.PhH := FrattiniSubgroup(H);
         r.wf5 := r.mkwf(r.PhH);
         ## data for the conditions of the next layer
         r.Tl5  := fail;   r.pos5 := fail;
         if r.dG5.m > 0 then
            r.Tl5 := r.linv(Concatenation(r.dG5.pi, [r.dG5.b]), r.dG5.m);
            if not (r.dG5.mu = fail or r.dH5.mu = fail) then
               r.pos5 := First(Cartesian([1..r.dG5.m], [1..2]),
                            q -> not IsZero(r.dG5.mu[q[1]][q[2]]));
               if r.pos5 = fail then r.Tl5 := fail; fi;
            elif not (r.dG5.b0 and r.dH5.b0) then
               r.Tl5 := fail;
            fi;
         fi;
         ## the p-power map on the canonical line, if there is one
         r.kG5 := fail;   r.kH5 := fail;
         if r.bs5.kind = "line" and not (r.dG5.kap = fail or r.dH5.kap = fail) then
            r.u1G5 := (r.bs5.PG^-1)[1];   r.u1H5 := r.bs5.PH[1];
            r.c5   := First([1..2], i -> not IsZero(r.u1H5[i]));
            r.kG5  := r.dG5.kap(r.u1G5);
            r.kH5  := r.dH5.kap(r.u1H5);
            if r.kG5 = fail or r.kH5 = fail or (IsZero(r.kG5) and IsZero(r.kH5)) then
               r.kG5 := fail;   r.kH5 := fail;
            fi;
         fi;
         r.el5 := IsElementaryAbelian(r.PhH);
         r.fH5 := Pcgs(r.dH5.V);
         r.cG  := List(r.pcgG, x -> r.one*ExponentsOfPcElement(r.dG5.f,
                          Image(r.dG5.nat, x)));
         ## one candidate: the images in V', lifted through Phi(H)
         r.n5 := 0;
         ## without the conditions of the next layer the candidates are many, so the
         ## work is bounded and the general search takes over if nothing is found
         if r.Tl5 = fail then r.lim5 := 800; else r.lim5 := 2000; fi;
         r.try5 := function(A)
            local im;
            if r.n5 > r.lim5 then return fail; fi;
            if not r.ok5(A, r.dG5, r.dH5) then return fail; fi;
            r.n5 := r.n5 + 1;
            im := List(r.cG, v -> PreImagesRepresentative(r.dH5.nat,
                          PcElementByExponents(r.fH5, List(v*A, IntFFE))));
            if r.el5 then return r.liftmodu(im, r.PhH, r.wf5); fi;
            return r.liftab(im, r.PhH, r.wf5);
         end;
         r.tryA5 := function(tot)
            local cd, i, s, t, a, A, new, pairs, q;
            ## the p-power layers, if they are available, give the strongest conditions
            if not r.dG5.tau = fail and not r.dH5.tau = fail then
               cd := r.tcands(r.dG5, r.dH5);
               if not cd = fail then
                  Info(myp5id, 3, "p5id_iso_random_bruteforce: (A5) ",
                       Length(cd), " candidates from the p-power layers");
                  for A in Permuted(cd, Random(SymmetricGroup(Length(cd)))) do
                     new := r.try5(A);
                     if not new = fail then return new; fi;
                  od;
               fi;
            fi;
            if r.bs5.kind = "free" then
               ## every alpha is admissible, so take them at random
               for i in [1..tot] do
                  new := r.try5(RandomInvertibleMat(2, GF(p)));
                  if not new = fail then return new; fi;
               od;
               return fail;
            fi;
            if r.bs5.kind = "vec" then
               ## alpha(v0) = det(alpha)*v0' forces the second diagonal entry
               cd := [];
               for s in r.units do
                  for a in AsList(GF(p)) do
                     Add(cd, r.bs5.PG*[[s, Zero(GF(p))], [a, r.bs5.dd^-1]]*r.bs5.PH);
                  od;
               od;
               for A in Permuted(cd, Random(SymmetricGroup(Length(cd)))) do
                  new := r.try5(A);
                  if not new = fail then return new; fi;
               od;
               return fail;
            fi;
            ## kind = "line": alpha = [[s,0],[a,t]] in the adapted basis; a is solved
            ## for if the next layer gives conditions, and run through otherwise
            pairs := Cartesian(r.units, r.units);
            pairs := Permuted(pairs, Random(SymmetricGroup(Length(pairs))));
            cd := [];
            for q in [1..Length(pairs)] do
               s := pairs[q][1];   t := pairs[q][2];
               if r.Tl5 = fail then
                  cd := Concatenation(cd, List(AsList(GF(p)),
                           a -> r.bs5.PG*[[s, Zero(GF(p))], [a, t]]*r.bs5.PH));
               else
                  A := List([0,1,2], a -> r.bs5.PG*[[s, Zero(GF(p))],
                                             [r.one*a, t]]*r.bs5.PH);
                  cd := Concatenation(cd, List(
                           r.solveq(r.res5(A[1], r.dG5, r.dH5),
                                    r.res5(A[2], r.dG5, r.dH5),
                                    r.res5(A[3], r.dG5, r.dH5)),
                           a -> r.bs5.PG*[[s, Zero(GF(p))], [a, t]]*r.bs5.PH));
               fi;
               if Length(cd) < 2000 and q < Length(pairs) then continue; fi;
               for A in Permuted(cd, Random(SymmetricGroup(Length(cd)))) do
                  new := r.try5(A);
                  if not new = fail then return new; fi;
               od;
               if r.n5 > r.lim5 then return fail; fi;
               cd := [];
            od;
            return fail;
         end;
         newim := r.tryA5(300);
         Info(myp5id, 3, "p5id_iso_random_bruteforce: (A5) kind ", r.bs5.kind,
              ", ", r.n5, " candidates tried");
         if not newim = fail then
            Info(myp5id, 2, "p5id_iso_random_bruteforce: case A5 for ",id);
            return newim;
         fi;
      fi;
   fi;

   ## ---------------------------------------------------------------------------
   ## (B) attempts: the admissible characteristic subgroups, smallest first
   ## ---------------------------------------------------------------------------
   r.cand  := r.chars(G);
   r.candH := r.chars(H);
   r.pos   := Filtered([1..Length(r.cand)], i -> Size(r.cand[i]) > 1);
   r.pos   := Filtered(r.pos, i -> not ForAny(r.pos, j -> j < i and r.cand[j] = r.cand[i]));
   SortBy(r.pos, i -> [Size(r.cand[i]), i]);
   r.qs := [];
   for k in r.pos do
      t := r.std(r.stdG(r.cand[k]), r.candH[k]);
      if t = fail then continue; fi;
      t.chr := true;            ## K is characteristic: a liftable isomorphism exists
      Add(r.qs, t);
      newim := r.lift(t.map, t.nat, t.natH, t.K);
      if not newim = fail then
         Info(myp5id, 2, "p5id_iso_random_bruteforce: case B for ",id);
         return newim;
      fi;
   od;

   ## ---------------------------------------------------------------------------
   ## (B2) the subgroups of order p of C are not characteristic, so there is no canonical
   ## partner in H: we fix one of them in G and run over all p+1 subgroups of order p of
   ## CH, keep those with G/K and H/KH isomorphic, and try to lift. This is complete
   ## because an isomorphism maps C onto CH; the quotients are larger than G/C and carry
   ## more information, and p+1 lifts are much cheaper than the random search in (C).
   ## ---------------------------------------------------------------------------
   if Length(Pcgs(C)) = 2 then
      gen  := Pcgs(C);
      genH := Pcgs(CH);
      r.K  := Subgroup(G, [gen[1]]);
      r.gK := r.stdG(r.K);          ## the same for all candidates KH below
      for k in [0..p] do
         if k = p then
            r.KH := Subgroup(H, [genH[1]]);
         else
            r.KH := Subgroup(H, [genH[2]*genH[1]^k]);
         fi;
         t := r.std(r.gK, r.KH);
         if t = fail then continue; fi;
         t.chr := false;      ## K is not characteristic here, so this quotient need
                              ## not admit a liftable isomorphism at all
         Add(r.qs, t);        ## still a candidate for the random search in (C): these
                              ## quotients are larger, and their index is much smaller
         newim := r.lift(t.map, t.nat, t.natH, t.K);
         if not newim = fail then
            Info(myp5id, 2, "p5id_iso_random_bruteforce: case B2 for ",id);
            return newim;
         fi;
      od;
   fi;

   ## ---------------------------------------------------------------------------
   ## (C) brute force. Some isomorphism G --> H exists and induces iso' = b*t.map on the
   ## quotient for some b in Aut(H/KH); since c*b*t.map lifts for every c in the image of
   ## Aut(H), the automorphisms that do the job form a coset of that image, and the
   ## expected number of random tries is its index. That index is out of reach for the
   ## groups still open here, so this is a bounded random search over all quotients
   ## collected in (B) and (B2), starting with the more promising ones. No orders of
   ## automorphism groups are computed; we only use that abelian quotients tend to have
   ## large automorphism groups and that large quotients are informative.
   ## ---------------------------------------------------------------------------
   if not r.qs = [] then
      ## all quotients from (B) and (B2) are used: those from (B2) are more promising
      ## (larger quotient, index smaller by about p), but only one of them lifts at all,
      ## so none may be dropped. For a characteristic K a liftable isomorphism is
      ## guaranteed to exist, for the others not; the former get half of the budget.
      SortBy(r.qs, x -> [not x.chr, IsAbelian(x.Q), -Size(x.Q)]);
      ## one try costs about 0.1 ms, essentially independent of p, so the total number
      ## r.tot of tries is a constant: roughly the seconds we are willing to spend times
      ## 5000. Raise it to trade time for coverage.
      r.tot := 10^6;
      r.nch := Number(r.qs, x -> x.chr);
      for t in r.qs do
         if t.chr then
            ## a liftable isomorphism is guaranteed here, so these quotients get the
            ## bulk of the budget
            itCH := QuoInt(r.tot, r.nch);
         else
            itCH := Maximum(50, QuoInt(r.tot, 5*(Length(r.qs)-r.nch)));
         fi;
         adj    := AutomorphismGroup(t.Q);
         r.gens := Concatenation(GeneratorsOfGroup(adj),
                                 List(GeneratorsOfGroup(adj), x -> x^-1));
         r.im   := List(r.pcgG, x -> Image(t.map, Image(t.nat, x)));
         for k in [1..itCH] do
            ## a few steps of a random walk on Aut(H/K), carried out on the images
            ## only; this avoids composing random automorphisms, which would dominate
            ## the cost. Consecutive tries have to be decorrelated, so one step is not
            ## enough; on the other hand the test below discards most candidates after
            ## one or two relations, so a long walk is not worth its price either.
            for j in [1..5] do
               r.g  := Random(r.gens);
               r.im := List(r.im, y -> Image(r.g, y));
            od;
            newim := r.liftu(r.im, t.natH, t.K);
            if not newim = fail then
               Info(myp5id, 2, "p5id_iso_random_bruteforce: case C for ",id);
               return newim;
            fi;
         od;
      od;
   fi;


################################################################################# END OF CLAUDE CODE!!!!!


    return fail;
 
end;












####################################################################################
####################################################################################
####################################################################################
####################################################################################
####################################################################################
##
##
## MAIN FUNCTIONS
##
####################################################################################
####################################################################################
####################################################################################
####################################################################################




####################################################################################
##
## input: p-group of order dividing p^5
## output: IdSmallGroup
##
p5id_IdSmallGroup := function(G)
local id;
   if HasIdGroup(G) then return IdSmallGroup(G); fi;
   id := p5id_Idp5Group(G);
   if not id.iso = fail then G!.isoToStd := id.iso; fi;
   return id.id;
end;


####################################################################################
##
## input: p-group G of order dividing p^5
## output: isomorphism to SmallGroup(IdSmallGroup(G))
## N.B.: for groups of order p^5 the current algorithm is randomised and might fail
##       in this case, "fail" is returned and it is recommended to start again
##       or use ANUPQ
##
p5id_IsomorphismSmallGroup := function(G)
local isopc, GG, id, iso,p,f;
   if Size(G)=1 then return IsomorphismGroups(G,SmallGroup(1,1)); fi;
   f := Collected(FactorsInt(Size(G)));
   if not Size(f)=1 or not f[1][2] <= 5 then Error("wrong input"); fi;
   f := f[1];
   if IsBound(G!.isoToStd) then return G!.isoToStd; fi;     ##!!!
   if not IsPcGroup(G) then
      isopc := IsomorphismPcGroup(G);
      GG := Image(isopc);
   else
      isopc := GroupHomomorphismByImages(G,G);
      GG := G;
   fi;
   if HasIdGroup(G) then SetIdGroup(GG,IdSmallGroup(G)); fi;
   id := p5id_IdSmallGroup(GG);
   if f[2]<5 or f[1] in [2,3]  then
      id := p5id_Idp5Group(GG);
      if not id.iso = fail then
	 G!.isoToStd := isopc*id.iso;                        ##!!
         return G!.isoToStd;
      fi;
   fi; 
   iso := p5id_iso_random_bruteforce(GG);
   if not iso=fail then
      G!.isoToStd := isopc*iso;
      return isopc*iso;
   fi; 
   Display("#I p5id_IsomorphismSmallGroup random algorithm failed; please try again or use ANUPQ");
   return fail;
end;


####################################################################################
##
## method for groups of order p^i with i<=5
##
InstallMethod( IsomorphismSmallGroup,
    "for groups of order p^i with i<= 5 and p>5, via p5id_IdSmallGroup",
    [ IsGroup ],
    SUM_FLAGS,   # rank this above the SmallGrp library methods
function( G )
    local n, f;
    if not IsFinite( G ) then
        TryNextMethod();
    fi;
    n := Size( G );
    if n = 1 then return IsomorphismGroups(G,SmallGroup(1,1)); fi;
    f := Collected(FactorsInt(n));
    if not Size(f)=1 or not f[1][2] <= 5  then 
        TryNextMethod();
    fi;
    return p5id_IsomorphismSmallGroup( G );
end );


####################################################################################
##
## method for groups of order p^i with i<=5
##
InstallMethod( IdSmallGroup,
    "for groups of order p^i with i<= 5 and p>5, via p5id_IdSmallGroup",
    [ IsGroup ],
    SUM_FLAGS,   # rank this above the SmallGrp library methods
function( G )
    local n, f;
    if not IsFinite( G ) then
        TryNextMethod();
    fi;
    n := Size( G );
    if n = 1 then SetIdGroup(G,[1,1]); return [1,1]; fi;
    f := Collected(FactorsInt(n));
    if not Size(f)=1 or not f[1][2] <= 5 or not f[1][1]>5 then 
        TryNextMethod();
    fi;
   #Display("new code!");
    return p5id_IdSmallGroup( G );
end );






#####################################################################################
#####################################################################################
#####################################################################################
#####################################################################################
#####################################################################################
##
##
## TEST SUITE
##
##



p5id_random_spcgscopy := function(G)
    local new, max, C, M, Gpc, g, hom, Q;
    return PcGroupCode(RandomSpecialPcgsCoded(G), Size(G));
end;

p5id_random_pccopy := function(G)
    local new, max, C, M, Gpc, g, hom, Q;

    if not IsPcGroup(G) then return G; fi;
    new := [];
    if Size(G) = 1 then return G; fi;
    max := MaximalSubgroupClassReps(G);
    C   := G;
    M   := Random(max);
    while Size(M)>1 do
        hom    := NaturalHomomorphismByNormalSubgroup(C,M);
        Q      := Image(hom);
        repeat g := Random(Q); until not g = g^0;
        Add(new,PreImagesRepresentative(hom,g));
        C   := M;
        max := MaximalSubgroupClassReps(M);
        M   := Random(max);
    od;
    repeat g:= Random(C); until not g in M;
    Add(new, g);
    new := PcgsByPcSequenceNC(FamilyObj(One(G)),new);
    Assert(0, Product(RelativeOrders(new)) = Size(G));
    Gpc := PcGroupWithPcgs(new);
    return Gpc;
end;

p5id_random_pcgscopy := function(G)
    local pcg, n, p, new, i, j, g;

    if not IsPcGroup(G) then return G; fi;
    pcg := Pcgs(G);
    n   := Length(pcg);
    p   := RelativeOrders(pcg)[1];
    new := [];
    for i in [1..n] do
        g := pcg[i]^Random([1..p-1]);
        for j in [i+1..n] do
            g := g * pcg[j]^Random([0..p-1]);
        od;
        Add(new, g);
    od;
    return PcGroupWithPcgs(PcgsByPcSequenceNC(FamilyObj(One(G)), new));
end;



p5id_random_permcopy := function(G)
   local pcg, n, p, new, i, j, g;
   pcg := Image(IsomorphismPermGroup(G));
   repeat new := List([1..8],x->Random(pcg)); g := Group(new); until g=pcg;
   return g;
end;


#####################################################################################
##
## TestSmallGroupID_p5
##
## input:  a list lps of primes, the number nr of random copies to test, boolean testIso
##
## For every p in lps and every i in [1..NumberSmallGroups(p^5)] we construct nr random
## copies of SmallGroup(p^5,i), compute the ID with IdSmallGroup_p5, and check that it
## is correct. If testIso is true, then we also construct the isomorphism onto
## SmallGroup(p^5,i) with IsomorphismSmallGroup and verify that it is a bijective
## homomorphism; if the randomised search returns fail, then this is reported. For each
## copy the runtime of the ID and of the isomorphism is displayed. Displays report 
## on 10 largest runtimes
##
TestSmallGroupID_p5 := function(lps, nr, testIso)
local idtimes, isotimes, wrong, failed, notiso, p, i, k, j, H, G, id, iso,
          t, tid, tiso, ok, x, y, l, report, e;

    idtimes  := [];
    isotimes := [];
    wrong    := [];
    failed   := [];
    notiso   := [];

    ## the ten largest entries of a list of triples [time, p, i]
    report := function(l, what)
        local av, s;
        if l = [] then return; fi;
        av := Sum(l, x -> x[1])/Length(l);
        Print("average time for ",what,": ",Int(av)," ms   (",Length(l)," tests)\n");
        s := ShallowCopy(l);
        SortBy(s, x -> -x[1]);
        Print("ten largest runtimes for ",what,":\n");
        for x in s{[1..Minimum(10,Length(s))]} do
            Print("   ",x[1]," ms   for SmallGroup(",x[2],"^5,",x[3],")\n");
        od;
    end;

    for p in lps do
        Print("------ start p = ",p,"\n");
	for e in [1,2,3,4] do
	for i in [1..NumberSmallGroups(p^e)] do
            H := SmallGroup(p^e,i);
            for k in [1..nr] do
                G   := p5id_random_pcgscopy(H);
	       #G   := p5id_random_permcopy(H);
                t   := Runtime();
                id  := IdSmallGroup(G); ### new!
                tid := Runtime()-t;
                if not id = [p^e,i] then
                    Error("ID WRONG for ",[p^e,i],": got ",id,"\n");
                fi;
                if not testIso then
                    Print("ID [",p,"^",e,",",i,"] copy ",k,":  id ",tid," ms\n");
                else
                    t    := Runtime();
                    iso  := IsomorphismSmallGroup(G);
                    tiso := Runtime()-t;
                    if iso = fail then
                        Error("ID [",p,"^e,",i,"] copy ",k,":  id ",tid," ms,  iso ",tiso," ms,  iso failed\n");
                    else
                         iso := GroupHomomorphismByImages(Source(iso),Range(iso),
			        GeneratorsOfGroup(Source(iso)),
				  List(List(GeneratorsOfGroup(Source(iso)),u->Image(iso,u))));
                        if not (not iso=fail and IsBijective(iso) and Source(iso) = G) then 
                            Error("iso wrong  for ",[p^e,i],"\n");
                        fi;
                        Print("ID [",p,"^",e,",",i,"] copy ",k,":   id ",tid," ms,  iso ",tiso," ms\n");
                    fi;
                fi;
            od;
        od;
	od;
        for i in [1..NumberSmallGroups(p^5)] do
            H := SmallGroup(p^5,i);
            for k in [1..nr] do
               
	        G   := p5id_random_pcgscopy(H);
	        #G   := p5id_random_permcopy(H);
		
                t   := Runtime();
                id  := IdSmallGroup(G); ### new !!
                tid := Runtime()-t;
                Add(idtimes, [tid, p, i]);
                if not id = [p^5,i] then
                    Add(wrong, [p, i, id]);
                    Error("ID WRONG for ",[p^5,i],": got ",id,"\n");
                fi;
                if not testIso then 
                    Print("ID [",p,"^5,",i,"] copy ",k,":  id ",tid," ms\n");
                else
                    t    := Runtime();
                    iso  := IsomorphismSmallGroup(G);
                    tiso := Runtime()-t;
                    Add(isotimes, [tiso, p, i]);
                    if iso = fail then
                        Add(failed, [p, i]);
                        Print("ID [",p,"^5,",i,"] copy ",k,":  id ",tid," ms,  iso ",tiso,
                              " ms,  random search failed\n");
                    else
		        iso := GroupHomomorphismByImages(Source(iso),Range(iso),
			        GeneratorsOfGroup(Source(iso)),
				  List(List(GeneratorsOfGroup(Source(iso)),u->Image(iso,u))));
                         if not (not iso=fail and IsBijective(iso) and Source(iso) = G) then 
                            Add(notiso, [p, i]);
                            Error("iso wrong  for ",[p^5,i],"\n");
                        fi;
                        Print("ID [",p,"^5,",i,"] copy ",k,":   id ",tid," ms,  iso ",tiso," ms\n");
                    fi;
                fi;
            od;
        od;
    od;

    Print("\n------ summary\n");
    report(idtimes, "ID");
    if testIso then report(isotimes, "iso"); fi;
    Print("wrong IDs: ",Length(wrong),
          ",  isomorphism search failed: ",Length(failed),
          ",  returned map not an isomorphism: ",Length(notiso),"\n");
    if not failed = [] then Print("   search failed for: ",failed,"\n"); fi;
    if not wrong = [] then Error("we have incorrect ids ",wrong); fi;
    if not notiso = [] then Error("we have incorrect isomorphisms ",notiso); fi;
    return rec(id := idtimes, iso := isotimes, wrong := wrong,
               failed := failed, notiso := notiso);
end;





