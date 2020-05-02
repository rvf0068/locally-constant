  
CHK_GOOD0:=function(g1,g2,morph)
  local w0,w,fw,deg3,h1;
  h1:=g1!.ParentGraph;
  w:=Length(morph);fw:=morph[w];w0:=VertexNames(g1)[w]; 
  deg3:=VertexDegree(h1,w0)+VertexDegree(g2,fw)-VertexDegree(g1,w);
  if deg3<=Order(g2) then 
     return true; 
  else
     return false; 
  fi;
end;

OrbitsL:=function(L) 
   local gamma,orbs;
   gamma:=AutomorphismGroup(L);
   orbs:=Orbits(gamma,[1..Order(L)],OnPoints);
   return orbs;
end;

eH:=function(L,i,j,orbs)
    local r,H,H1,x,y,B,alfa,Nx,Ny,l,ln,I,z,Lalfa,flag,Adx,Ady;
    l:=Order(L);
    r:=Length(orbs);
    if i<1 or j<i or r<j then return false; fi;   
    x:=orbs[i][1];
    y:=orbs[j][1];        
    B:=GraphByWalks([1,3],[2,4]);
    H:=GraphSum(B,[TrivialGraph,TrivialGraph,L,L]); # x.y.L.L
    Nx:=Concatenation([1,y+2],Adjacency(L,y)+2);
    Adx:=Adjacency(L,x);
    Ady:=Adjacency(L,y);
    if Ady=[] or Adx=[] then
       if Adx=Ady then 
          Lalfa:=[[]]; #degenerate isomorphism between empty graphs.
       else
          return false;
       fi; 
    else
       Lalfa:=IsoMorphisms(Link(L,y),Link(L,x));
    fi;
    if Lalfa=[] then return false; fi;

    for alfa in Lalfa do
        flag:=true;
        ln:=Length(alfa);
        Ny:=List([1..ln],z-> Adjacency(L,x)[alfa[z]]+l+2);
        Ny:=Concatenation([x+l+2,2],Ny);
        H1:=QuotientGraph(H,Nx,Ny);  
        I:=Intersection(Adjacency(H1,1),Adjacency(H1,2));
        for z in I do
           if NextPropertyMorphism(Link(H1,z),L,[],[CHK_MONO,CHK_MORPH,CHK_GOOD0])=fail then 
                flag:=false; break; 
           fi;
        od;
        if flag=true then return true; fi;
    od;
    return false;
    #return H;
end;

X01:=function(L,orbs) 
   local r,LE,i,j;
   r:=Length(orbs);
   LE:=[];
   for i in [1..r] do 
     for j in [i..r] do
        if eH(L,i,j,orbs) then
           Add(LE,[i,j]);
        fi;
     od;
   od;
   return LE;
end;

Count:=function(z,p) 
    return Length(Filtered(p,e->e=z));
end;

Diof:=function(L) 
   local orbs,r,LP,M;
   orbs:=OrbitsL(L);
   r:=Length(orbs);
   LP:=X01(L,orbs);
   M:=List([1..r],z->List(LP,p->Count(z,p)));
   M:=List([1..r],z->Concatenation(M[z],[-Length(orbs[z])]));
   return M;
end;

