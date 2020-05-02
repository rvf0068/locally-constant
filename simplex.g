
CountProperty:=function(L,P) 
    return Length(Filtered(L,P));
end;

ExchangeColumns:=function(M,c1,c2) 
    local temp,r;
    r:=Length(M);
    temp:=M{[1..r]}[c1];
    M{[1..r]}[c1]:=M{[1..r]}[c2];
    M{[1..r]}[c2]:=temp;
end;

ExchangeRows:=function(M,r1,r2) 
    local temp;
    temp:=M[r1];
    M[r1]:=M[r2];
    M[r2]:=temp;
end;

ExchangeColumnsAndRows:=function(M,r1,c1,r2,c2) 
    ExchangeColumns(M,c1,c2);
    ExchangeRows(M,r1,r2);
end;

AddRowK:=function(M,r1,r2,k) 
    M[r1]:=M[r1]+k*M[r2];
end;

AddRow:=function(M,r1,r2) 
    M[r1]:=M[r1]+M[r2];
end;

SubRow:=function(M,r1,r2) 
    M[r1]:=M[r1]-M[r2];
end;

MultRowK:=function(M,r,k) 
    M[r]:=k*M[r];
end;

EliminateInOtherRows:=function(M,r,c) #FIXME error handling
    local r1,r2;
    r1:=Length(M);
    for r2 in Union([1..r-1],[r+1..r1]) do 
       AddRowK(M,r2,r,-M[r2][c]);
    od; 
end;

Elimination:=function(M) #FIXME error handling
    local r,c,r1,i,j,bv;
    r:=Length(M); c:=Length(M[1]);r1:=1;bv:=[];
    for j in [1..c] do 
       i:=PositionProperty(M{[r1..r]}[j],x->x<>0);
       if i=fail then continue; fi;
       i:=i+r1-1;
       ExchangeRows(M,r1,i);
       bv[r1]:=j;
       MultRowK(M,r1,1/M[r1][j]);
       EliminateInOtherRows(M,r1,j);
       if r1=r then break; fi;
       r1:=r1+1;
    od;
   return bv;
end;

DiscardZeroRows:=function(M)
    local r,r1,c;
    r:=Length(M);c:=Length(M[1]);
    for r1 in [r,r-1..1] do 
      if CountProperty(M[r1],z->z=0)=c then
         Remove(M,r1);
      fi;
    od;
end;

IsInconsistent:=function(T)
   local c;
   c:=Length(T[1]);
   if CountProperty(T,row->row[c]<>0 and Set(row{[1..c-1]})=[0])>0 then 
       return true; 
   fi; 
   return false;
end;


easysol:=function(T,bv) 
  local r,r1,c,c1,sol,x;
  r:=Length(T); c:=Length(T[1]);
  sol:=List([1..c-1],z->0);
  for x in bv do
     sol[x]:=T[Position(T{[1..r]}[x],1)][c]; 
  od;
  return sol;
end;

Tableau:=function(T) 
   local T1,r,c,b,I,row,i,j;
   r:=Length(T); c:=Length(T[1]);
   for i in [1..r] do 
     if T[i][c]<0 then
        MultRowK(T,i,-1); 
     fi;
   od;
   b:=T{[1..r]}[c];
   T[r+1]:=[];
   T{[2..r+1]}:=T{[1..r]};
   I:=IdentityMat(r);
   T[1]:=List([1..c+r],function(z) if z<c then return 0; elif z<c+r then return -1; else return 0; fi; end);
   for i in [2..r+1] do 
      T[i]{[c..c+r-1]}:=I[i-1];
   od;
   T{[2..r+1]}[r+c]:=b;
end;

priceout:=function(T,bv) 
   local i;
   for i in [1..Length(bv)] do; 
     EliminateInOtherRows(T,i+1,bv[i]);
   od; 
end;

SelEntVar:=function(T)
   local c,ent;
    c:=Length(T[1]);
    return PositionProperty(T[1]{[1..c-1]},z->z>0);
end;

MinimumPosition:=function(L) 
   local min,i,pos;
   if L=[] then return fail; fi;
   min:=L[1];pos:=1;
   for i in [1..Length(L)] do 
      if min>L[i] then 
         min:=L[i]; pos:=i;
      fi;
   od; 
   return pos;
end;

SelLeavVar:=function(T,bv,c1) #changes bv
   local r,leav,min,pos,c,c2,bvl;
   r:=Length(T);c:=Length(T[1]);
   pos:=Filtered([2..r],z->T[z][c1]>0);
   if pos=[] then return fail; fi;
   leav:=MinimumPosition(List(pos,z->T[z][c]/T[z][c1]));
   leav:=pos[leav];   
   bvl:=PositionProperty([1..Length(bv)],z->T[leav][bv[z]]=1);
   bv[bvl]:=c1;
   return leav;
end;

NonNegativeSolution:=function(M,b) #FIXME error handling
    local T,i,j,r,r0,r1,r2,c,c0,c1,c2,Z,row,column,bv;
    T:=StructuralCopy(M); r:=Length(T); c:=Length(T[1]); 
    for i in [1..r] do Add(T[i],b[i]); od; 
    
    bv:=Elimination(T); 
    DiscardZeroRows(T);r:=Length(T);
    if IsInconsistent(T) then return fail; fi;
    if CountProperty(T{[1..r]}[c+1],z->z>=0)=r then
      return easysol(T,bv);
    fi;
    ## simplex.
    #Print("+");
    r0:=r;c0:=c;
    Tableau(T);
    c:=Length(T[1])-1;bv:=[c0+1..c0+r0];
    priceout(T,bv);
    while(T[1][c+1]>0) do 
       c1:=SelEntVar(T);
       if c1=fail then return fail; fi;
       r1:=SelLeavVar(T,bv,c1);#changes bv
       MultRowK(T,r1,1/T[r1][c1]);
       priceout(T,bv);
    od;
    return easysol(T,bv);
end;

HasNonNegativeSolution:=function(T,b)
    return NonNegativeSolution(T,b)<>fail;
end;

HasSemiPositiveSolution:=function(T) 
    local r,c,b,i;
    r:=Length(T); c:=Length(T[1]);
    if HasNonNegativeSolution(T,-T{[1..r]}[c]) then return 1; fi;
    return 0;
end;
#################################################

