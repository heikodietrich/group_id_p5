This is the pre-release GAP code accompanying the paper

  "Group identification for the groups of order dividing $p^5$"

by Heiko Dietrich, Bettina Eick, and Henrik Schanze.

Eventually this code will be distributed as a future GAP-package.

Main file: Idp5.g

Once loaded, the code provides a method `IdSmallGroup` for input groups that are $p$-groups of order dividing $p^5$ where $p$ is any prime. It returns the ID as defined in the `SmallGroups Library`.

The code also defines an attribute `IsomorphismSmallGroup` and provides a method for the groups considered here: for an input group G it computes an isomorphism $G\to \text{SmallGroup}(\text{IdSmallGroup}(G))$. 

N.B.: for groups of order dividing $p^4$ this algorithm is deterministic and will always terminate. The algorithm for $p^5$ reduces to the isomorphism problem for groups of order dividing $p^4$ and considers lifts; this is partly randomised and the implementation of this case has been developed with the LLM Claude Opus. While it can in principle return fail, this has not been observed in practice.

Example usage:

```gap
gap> ### get random group
gap> R := SmallGroup(7^5,65);;
gap> R := Image(IsomorphismPermGroup(R));;
gap> repeat gens := List([1..8],x->Random(R)); until Group(gens)=R;;
gap> R := Group(gens);;
gap> R := Image(IsomorphismPcGroup(R));;
gap>
gap> ### construct ID
gap> IdSmallGroup(R);
[ 16807, 65 ]
gap>
gap> ### get iso to standard copy
gap> iso := IsomorphismSmallGroup(R);;
gap>
gap> ### Image(iso) is canonically isomorphic to H := SmallGroup(7^5,65):
gap> ### We have Image(iso) <> H, but mapping Pcgs(Image(iso))
gap> ### to Pcgs(SmallGroup(IdSmallGroup(R))) defines an isomorphisms;
gap> ### demonstrate this:
gap> H := SmallGroup(7^5,65);;
gap> isoRtoH := iso * GroupHomomorphismByImages(Image(iso),H,Pcgs(Image(iso)),Pcgs(H));;
gap> Source(isoRtoH)=R and Image(isoRtoH)=H and IsBijective(isoRtoH);
true
```

The test function `TestSmallGroupId_p5` takes as input a list `lps` of primes, an integer `nr`, and a Boolean `testIso`; it will then run over `nr` copies of groups of order $p^i$ where $p$ lies in `lps` and $i\in\{1,2,3,4,5\}$ and tests that `IdSmallGroup` is computed correctly. If the Boolean `testIso` is true, then it also tests the isomorphism construction. It outputs statistics of the runtimes.

Example test:

```gap
gap> t:= TestSmallGroupID_p5([37,63,101],1,true);;
------ start p = 37
ID [37^1,1] copy 1:   id 2 ms,  iso 0 ms
ID [37^2,1] copy 1:   id 1 ms,  iso 0 ms
ID [37^2,2] copy 1:   id 1 ms,  iso 0 ms
...
ID [101^5,267] copy 1:   id 1 ms,  iso 11 ms
ID [101^5,268] copy 1:   id 3 ms,  iso 31 ms
ID [101^5,269] copy 1:   id 1 ms,  iso 1 ms

------ summary
average time for ID: 51 ms   (607 tests)
ten largest runtimes for ID:
   273 ms   for SmallGroup(101^5,257)
   235 ms   for SmallGroup(101^5,256)
   187 ms   for SmallGroup(101^5,120)
   163 ms   for SmallGroup(101^5,121)
   157 ms   for SmallGroup(101^5,214)
   156 ms   for SmallGroup(101^5,149)
   154 ms   for SmallGroup(101^5,155)
   153 ms   for SmallGroup(101^5,199)
   153 ms   for SmallGroup(101^5,184)
   152 ms   for SmallGroup(101^5,234)
average time for iso: 71 ms   (607 tests)
ten largest runtimes for iso:
   3187 ms   for SmallGroup(101^5,125)
   1595 ms   for SmallGroup(101^5,119)
   1589 ms   for SmallGroup(101^5,121)
   1584 ms   for SmallGroup(101^5,120)
   1305 ms   for SmallGroup(101^5,259)
   1245 ms   for SmallGroup(61^5,85)
   1244 ms   for SmallGroup(101^5,262)
   897 ms   for SmallGroup(61^5,184)
   806 ms   for SmallGroup(101^5,258)
   694 ms   for SmallGroup(101^5,130)
wrong IDs: 0,  isomorphism search failed: 0,  returned map not an isomorphism: 0
```


