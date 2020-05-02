AuxInfo:="/dev/null";
AuxInfo1:="/dev/tty";
MaxTime:=60;

CanLab:=function(G) #canonical labelling using nauty
   local i,j,str,canlab;
   if IsBound(G!.CanLab) then return G!.CanLab; fi;
   str:="n=";
   Append(str,String(Order(G)));
   Append(str," t");
   for i in Vertices(G) do 
      for j in [i+1..Order(G)] do 
         if IsEdge(G,[i,j]) then 
           Add(str,'1');
         else 
           Add(str,'0');
         fi;
      od;
   od;
   Append(str," q ");

   canlab:=YAGSExec("canlab",str);
   Remove(canlab);#remove trailing newline.

   G!.CanLab:=canlab;
   return canlab;
end;

IsIso:=function(G,H) 
   return CanLab(G)=CanLab(H);
end;

AddUptoIso:=function(L,x)
   local i,j,k,med,canlab;
   i:=1;j:=Length(L);
   canlab:=CanLab(x);
   if Length(L)=0 or CanLab(L[j])<canlab then 
        Add(L,x); 
        return; 
   fi;
   if CanLab(L[i])>canlab then 
      for k in [Length(L)+1,Length(L)..2] do 
        L[k]:=L[k-1]; 
      od;
      L[1]:=x;
      return; 
   fi;
   if CanLab(L[j])=canlab or CanLab(L[i])=canlab then return; fi;
   med:=Int((i+j)/2);
   repeat
      if CanLab(L[med]) < canlab then 
         i:=med;med:=Int((i+j)/2);
      elif CanLab(L[med]) > canlab then 
         j:=med;med:=Int((i+j)/2);
      else #CanLab(L[med]) = canlab
         return; 
      fi;
   until i=med;
   for k in [Length(L)+1,Length(L)..med+2] do 
      L[k]:=L[k-1];
   od;
   L[med+1]:=x; 
end;

AddUptoIso1:=function(L,x)
   if not ForAny(L,y->IsIso(x,y)) then
     Add(L,x);
   fi;
end;

Pairs:=function(S) 
   local P,i,j;
   P:=[];
   for i in [1..Length(S)] do 
     for j in [i+1..Length(S)] do 
        Add(P,[S[i],S[j]]);
     od;
   od;
   return P;
end;

CHK_GOOD:=function(g1,g2,morph)
  local w0,w,fw,deg3,deg3def,h1;
  h1:=g1!.ParentGraph;
  w:=Length(morph);fw:=morph[w];w0:=VertexNames(g1)[w]; 
  deg3:=VertexDegree(h1,w0)+VertexDegree(g2,fw)-VertexDegree(g1,w);
  deg3def:=VertexDegree(h1,w0)+VertexDegree(g2,fw)-VertexDegree(g1,w)-g1!.defx;
  if w in g1!.done then 
     return deg3=Order(g2); 
  else
     return deg3def<=Order(g2); 
  fi;
end;

CHK_GOOD2:=function(L,SH,g)
  local w,gw,w0,H,N,f,x,Defx,Range,s,Rangef,wn,wh;
  H:=SH!.sub;N:=SH!.N;Defx:=SH!.Defx;
  f:=SH!.f;x:=SH!.x;Range:=Adjacency(SH,x);
  Rangef:=Set(f);
  w:=Length(g);gw:=g[w];
  if w in Rangef then #check that f and g coincide
    wn:=Position(f,w);wh:=VertexNames(N)[wn];
    if not wh = gw then return false; fi; 
  fi;
  if not gw in Range then return false; fi;
  if gw in Vertices(H) then #check that g covers all edges of H in Im(g).
     for s in [1..Length(g)-1] do
      if g[s] in Vertices(H) and IsEdge(H,[gw,g[s]]) and not IsEdge(L,[w,s]) then
         return false; 
      fi; 
     od;
  else # gw in Defx
     if ForAny(Defx, s-> s < gw and not s in g ) then 
        return false; #when using Defx, always use small numbers first.
     fi; 
  fi;
  return true;
end;

Dequeue1:=function(LH) 
   return Remove(LH,1);
end;

Dequeue:=function(LH) 
   local n,i,pos,numdone;
   n:=Order(LH[1]);pos:=1;
   numdone:=Length(LH[1]!.done);
   for i in [1..Length(LH)] do 
      if Order(LH[i]) > n then break; fi;
      if Length(LH[i]!.done)>numdone then 
         pos:=i;
         numdone:=Length(LH[i]!.done);
      fi;
   od;
   return Remove(LH,pos);
end;

RepModAut:=function(L,aut) 
    local L0,f,g;
    L0:=[];
    for f in L do
       if ForAny(aut,g->List(f,f->f^g) in L0) then continue; fi;
       Add(L0,f);
    od;
    return L0;
end;

Inclusions:=function(H,L,x,N)
   local Lf,Instance,pos;
   if Order(N)>Order(L) then return []; fi;
   N!.done:=Filtered(Vertices(N),z->VertexNames(N)[z] in N!.ParentGraph!.done);
   N!.defx:=Order(L)-VertexDegree(H,x);#deficit of x.
   N!.Hdegs:=List(Vertices(N),z->VertexDegree(H,VertexNames(N)[z]));
#Begin Dynamic Programming---
   Instance:=[AdjMatrix(N),N!.done,N!.Hdegs];
   pos:=PositionSorted(L!.inc[1],Instance);
   if pos<=Length(L!.inc[1]) and L!.inc[1][pos]=Instance then return L!.inc[2][pos]; fi;
#End DP ---
   Lf:= PropertyMorphisms(N,L,[CHK_MONO,CHK_MORPH,CHK_GOOD]);
   Lf:=RepModAut(Lf,AutomorphismGroup(L)); #reducir mod Aut(L);
#Begin DP---
   AddSet(L!.inc[1],Instance);
   InsertElmList(L!.inc[2],pos,Lf);
   if Length(L!.inc[1])<> Length(L!.inc[2]) then Error("Length mismatch in Inclusions()"); fi;
#End DP---
   return Lf;
end;

IsPartialExtension:=function(H,L) 
  local cand,undone,vd,ext,x,N,defx,vdN,vdL;
  vd:=VertexDegrees(H);
  if Maximum(vd)> Order(L) then return false; fi;
  if not IsBound(H!.done) then #only happens at the very beginning, when H=Cone(L).
     H!.done:=[1];
     H!.section:=List(Vertices(H),function(x) if x=1 then return 1; fi; return 2; end);
     H!.minsection:=2;
     H!.maxsection:=2;
  fi;
  cand:=Difference(Vertices(H),H!.done);
  cand:=Filtered(cand,x->VertexDegree(H,x)=Order(L));
  cand:=Filtered(cand,x->IsIso(Link(H,x),L));
  UniteSet(H!.done,cand);
  undone:=List(Difference(Vertices(H),H!.done));
  if undone=[] then 
    H!.minsection:=infinity; #Is an extension! 
  else 
    H!.minsection:=Minimum(List(undone,x->H!.section[x]));
  fi;
  for x in undone do
     N:=Link(H,x);
     vdN:=SortedList(VertexDegrees(N));
     vdL:=SortedList(VertexDegrees(L));
     while vdN<>[]  do
       if Remove(vdN) > Remove(vdL) then 
         return false;
       fi;
     od;
     if Inclusions(H,L,x,N)=[] then return false; fi;
  od;
  return true;
end; 

ChooseWisely:=function(H,L) 
   local cand,x,degsdone,degs,max1,max2;
   if H!.minsection = infinity then 
      return fail; 
   fi;
   cand:=Filtered(Vertices(H),x->H!.section[x]=H!.minsection and not x in H!.done);
   if cand=[] then 
     Error("No candidates for x!!!");
   fi;
   degsdone:=List(cand,x->Length(Intersection(H!.done,Adjacency(H,x))));
   max1:=Maximum(degsdone);
   cand:=cand{Filtered([1..Length(cand)],i->degsdone[i]=max1)};
   return RandomList(cand);
end;


SuperGraph:=function(H,x,defx)    
   local undone,U,UP,E1,Defx,Vec;
   undone:=Filtered(Vertices(H),x->not x in H!.done);
   Defx:=List([1..defx],w->w+Order(H));
   U:=Filtered(Vertices(H),u-> #nuevos posibles vecinos de x
          not u=x and
          not u in H!.done and 
          not IsEdge(H,[u,x]) and
          Intersection(Adjacency(H,u),Adjacency(H,x),H!.done)=[]
      );
   Vec:=Difference(Union(U,Adjacency(H,x)),H!.done);
   UP:=Filtered(Pairs(Vec),p-> #nuevas posibles aristas entre vecinos posibles de x
           not IsEdge(H,p) and
           Intersection(Adjacency(H,p[1]),Adjacency(H,p[2]),H!.done)=[]
       );
   E1:=Union(Edges(H),Cartesian([x],U),UP,Cartesian(Defx,undone),Pairs(Defx));
   return GraphByEdges(E1);
end;

ExtensionAtXwFG:=function(H,L,x,g) 
   local E1,H1,Im,s,Defx;
   Im:=Set(g);
   E1:=Edges(H);
   UniteSet(E1,Cartesian([x],Im));
   UniteSet(E1,List(Edges(L),e->[g[e[1]],g[e[2]]]));
   H1:=GraphByEdges(E1);
   if Maximum(VertexDegrees(H1))>Order(L) then return fail; fi;
   H1!.done:=Union(H!.done,[x]);
   H1!.section:=ShallowCopy(H!.section);
   Defx:=Difference(Vertices(H1),Vertices(H));
   if Defx<>[] then 
      H1!.maxsection:=H!.maxsection+1;
      for s in Defx do 
         H1!.section[s]:=H1!.maxsection;
      od;
   else
      H1!.maxsection:=H!.maxsection;
   fi;
   if IsPartialExtension(H1,L) then 
      return H1;
   else
      return fail;
   fi;
end;

Reinclusions:=function(H,L,x,N,SH,f) 
   SH!.sub:=H;SH!.f:=f;SH!.x:=x;SH!.N:=N;
   SH!.Defx:=[1..Order(L)-VertexDegree(H,x)]+Order(H);
   return PropertyMorphisms(L,SH,[CHK_MONO,CHK_MORPH,CHK_GOOD2]);
end;

ExtensionsAtXwF:=function(H,L,x,N,SH,f) 
  local g,Lg,LH,H1;
  LH:=[];
  Lg:=Reinclusions(H,L,x,N,SH,f);
  for g in Lg do
     H1:=ExtensionAtXwFG(H,L,x,g);
     if H1<> fail then 
        AddUptoIso(LH,H1);
     fi;
  od;
  return LH;
end;

ExtensionsAtX:=function(H,L,x) 
   local N,Lf,f,LH,H1,SH;
   N:=Link(H,x);LH:=[];
   Lf:=Inclusions(H,L,x,N);
   SH:=SuperGraph(H,x,N!.defx); #The minimal supergraph containing all extensions of H at x.
   for f in Lf do 
      for H1 in ExtensionsAtXwF(H,L,x,N,SH,f) do
         AddUptoIso(LH,H1);
      od;
   od;
   return LH;
end;

Show:=function(LLH) 
    local str,i,S;
    str:=[];
    S:=Collected(List(LLH,Order));
    for i in [1..Length(S)] do 
      Append(str,String(S[i][1]));
      Append(str,"x");
      Append(str,String(S[i][2]));
      Append(str," ");
    od;
    return str;
end;

GenLoc:=function(L) 
     local aut,orbs,xL,H,LLH,x,h,t1,t2;
     t1:=TimeInSeconds();
     aut:=AutomorphismGroup(L); #automatically stored in L.
     L!.orbs:=Orbits(aut,[1..Order(L)],OnPoints); #store in L.
     L!.inc:=[[],[]]; #for dynamic programming of Inclusions();
     xL:=Cone(L);
     L!.ParentGraph:=xL;SetVertexNames(L,[2..Order(L)+1]); #Set L as induced subgraph of xL.
     LLH:=[]; 
     H:=CopyGraph(xL);
     IsPartialExtension(H,L);#mark finished vertices, etc.
     if H!.minsection=infinity then return H; fi;
     LLH:=[H];
     while LLH<>[] do
         t2:=TimeInSeconds();
         if t2-t1>MaxTime then 
            PrintTo(AuxInfo1,"\nTime out! \n");
            return 3;#not enough time;
         fi; 
         PrintTo(AuxInfo1,"Queued: ",Length(LLH)," Orders: ",Show(LLH),"            \r");
         H:=Dequeue(LLH);
         x:=ChooseWisely(H,L); 
         for h in ExtensionsAtX(H,L,x) do
            if h!.minsection=infinity then PrintTo(AuxInfo1,"\n");return h; fi;
            AddUptoIso(LLH,h);
         od;
     od;
     PrintTo(AuxInfo1,"\n");
     return fail;
end;


Ginfo:=function(H) 
   Print("done: ", H!.done,"\n");
   Print("section: ", H!.section,"\n");
   Print("minsection: ", H!.minsection,"\n");
   Print("maxsection: ", H!.maxsection,"\n");
end;
