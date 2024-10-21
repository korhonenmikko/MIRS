//
// D_st, for 1 <= s < t <= l
// acts by f_t -> f_t + e_s
//         f_s -> f_s + e_t
// other basis vectors fixed.
//
DmapGO := function(s,t,l)
 return 1+Matrix(GF(2), 2*l,2*l, [<s,2*l+1-t,1>, <t,2*l+1-s,1>]);
end function;

//
// 1 <= t <= l-1
// D_{t,l}' in GOMinus(2*l,2)
//
DmapminusGO := function(t,l)
 return 1+Matrix(GF(2), 2*l,2*l, [<t,l+1,1>, <l,2*l+1-t,1>, <t,2*l+1-t,1>]);
end function;

//
// C_t, for 1 <= t <= l
// acts by e_t -> f_t
//         f_t -> e_t
//         other basis vectors fixed.
// contained in GOPlus(2*l,2) and GOMinus(2*l,2)
//
CmapGO := function(t,l)
 return 1+Matrix(GF(2), 2*l,2*l, [<t,2*l+1-t,-1>, <2*l+1-t,t,1>, <t,t,-1>, <2*l+1-t, 2*l+1-t,-1>]); 
end function;

//
// E' in GOMinus(2*l,2):
// E' maps f_l -> f_l + e_l, and fixes remaining basis vectors.
// In MAGMA, basis for natural module of GOMinus(2*l,2) < Sp(2*l,2) is
// e_1, ..., e_{l-1}, e_l, f_l, ..., f_1
// (e_i, f_i) hyperbolic pairs
// Q(e_1) = ... = Q(e_{l-1}) = 0, Q(e_l) = 1.
// Q(f_1) = ... = Q(f_{l-1}) = 0, Q(f_l) = 1.
//
EmapGO := function(l)
 return 1+Matrix(GF(2),2*l,2*l,[<l,l+1,1>]);
end function;

//
// L := [v_1, ..., v_{2*l}]
// vector v = (v_1, ..., v_{2l}) in natural module for GOPlus(2l,2)
// v = v_1*e_1 + ... + v_l*e_l + v_{l+1}*f_l + ... + v_{2l}*f_1
// quadratic form:
// Q(e_i) = Q(f_j) = 0 for all i,j
// b(e_i,f_j) = 1 if i = j; and 0 otherwise. 
//
// Q(v) = v_1 * v_{2l} + ... + v_{l}*v_{l+1}
// return sequence [<i_1,j_1>, ..., <i_t,j_t>] such that...
//
// First define x = f(i_1,j_1) * ... * f(i_t,j_t)
// where f(i,j) = D_{i,j} if i < j and f(i,i) = C_i.
//
// if Q(v) = 0:
// x * v = e_1
//
// if Q(v) = 1:
// x * v = e_1+f_1
//
// where f(i,j) = D_{i,j} if i < j and f(i,i) = C_i.
//
// In MAGMA we get v * Transpose(x) = e_1 or e_1+f_1.
//
CDsequencePlus := function(v)

	if {x : x in v} eq {0} then
		return [];
	end if;

	l := #v div 2;
    // s = value under quadratic form
	s := &+[v[i]*v[2*l+1-i] : i in [1..l]];
	
	if l eq 1 then
		
		if s eq 1 then
			return [];
		end if;
		
		if s eq 0 then
		  if v[1] eq 1 then
			return [];
		  end if;
		  
		  return [<1,1>];
		end if;
		
	end if;
	
	// v = v'+v''
	// v' = c e_1 + d f_1
	// v'' in <e_2, f_2>, ..., <e_l, f_l>
	
	c := v[1];
	d := v[#v];
	
	Lp := [v[j] : j in [2..(#v-1)]];
    
	if {x : x in Lp} eq {0} then
		return $$([c,d]);
	end if;
	
	if s eq 0 then
	
		if (c eq 0) and (d eq 0) then
			g := [<x[1]+1,x[2]+1> : x in $$(Lp)];
			return [<1,1>, <1,2>, <1,1>, <2,2>, <1,2>, <2,2>] cat g;
		end if;
		
		if (c eq 0) and (d eq 1) then
			g := [<x[1]+1,x[2]+1> : x in $$(Lp)];
			return [<1,1>, <1,2>] cat g;
		end if;
		
		if (c eq 1) and (d eq 0) then
		    g := [<x[1]+1,x[2]+1> : x in $$(Lp)];
			return [<1,1>, <1,2>, <1,1>] cat g;	
		end if;
	
		if (c eq 1) and (d eq 1) then
			g := [<x[1]+1,x[2]+1> : x in $$(Lp)];
			return [<1,1>, <1,2>, <2,2>, <1,2>] cat g;
		end if;
	
	end if;
	
	if s eq 1 then
	
		if (c eq 0) and (d eq 0) then
			g := [<x[1]+1,x[2]+1> : x in $$(Lp)];
			return [<1,2>, <2,2>, <1,2>, <1,1>, <1,2>] cat g;
		end if;
		
		if (c eq 0) and (d eq 1) then
			g := [<x[1]+1,x[2]+1> : x in $$(Lp)];
			return [<1,2>, <2,2>, <1,2>] cat g;
		end if;
		
		if (c eq 1) and (d eq 0) then
		    g := [<x[1]+1,x[2]+1> : x in $$(Lp)];
			return [<1,2>, <2,2>, <1,2>, <1,1>] cat g;	
		end if;
	
		if (c eq 1) and (d eq 1) then
			g := [<x[1]+1,x[2]+1> : x in $$(Lp)];
			return [<1,2>] cat g;
		end if;
	
	end if;

	// this should never happen if v is valid sequence
	return [<-1000,-1000>];

end function;

// conjugate pairs (v,w) with Q(v) = Q(w) = 0, b(v,w) = 1 
// with an element of GOPlus(2*l,2) into the pair (e_1, f_1).
// in this function g in GOPlus(2l,2), with v = ge_1, w = gf_1. 
// i.e. v = e_1*Transpose(g) and w = f_1*Transpose(g)
// 
// This function returns a sequence S = [<i_1,j_1>, ..., <i_t,j_t>] such that:
//      First define x = f(i_1,j_1) * ... * f(i_t,j_t)
//      where f(i,j) = D_{i,j} if i < j and f(i,i) = C_i.
//      In other words x := CDseqtoeltPlus(S);
//
//      Then:  x*g*e_1 = e_1.
//             x*g*f_1 = f_1.
//
// In MAGMA, e_1*Transpose(x*g) = e_1.
//           f_1*Transpose(x*g) = f_1.
CDfirstpairPlus := function(g)

	l := #Rows(g) div 2;

	if l eq 1 then
		if Order(g) eq 1 then
			return [];
		end if;
		
		return [<1,1>];
	end if;

	// first column, i.e. image of e_1
	v := Transpose(g)[1];
	v := [v[j] : j in [1..#Rows(g)]];

	L := CDsequencePlus(v);
	h := g;

	// L -> L[1]*L[2]*...*L[#L] ...

	for i in [1..#L] do
		x := L[#L-i+1];
		if x[1] eq x[2] then
			h := CmapGO(x[1],l)*h;
		end if;
		if x[1] ne x[2] then
			h := DmapGO(x[1],x[2],l)*h;
		end if;
	end for;

    // Here h = L[1]*L[2]*...*L[#L]*g, so h*e_1 = e_1.
    // since 1 = b(hf_1,he_1) = b(hf_1,e_1), we get:
    // hf_1 = c * e_1 + w[1]*e_2 + ... + w[2*l-2]*f_2 + f_1 for some c
	c := h[1][2*l];
	w := [h[j][2*l] : j in [2..(2*l-1)]];

	if {x : x in w} eq {0} then
        // In this case h*f_1 = c*e_1 + f_1
        // We have      Q(h*f_1) = Q(f_1) = 0
        // Thus h*f_1 = f_1 in this case, and we are done.
		return L;
	end if;

    // D_{i,j} in O^+(2l-2,2) corresponds to D_{i+1,j+1} in O^+(2l,2). 
    // similarly C_i corresponds to C_{i+1} in O^+(2l,2).
	K := [<x[1]+1,x[2]+1> : x in CDsequencePlus(w)];

	if c eq 0 then
		return [<1,2>] cat K cat L;
	end if;

	if c eq 1 then   
		return [<1,2>, <2,2>, <1,2>] cat K cat L;
	end if;

	return [<-1000,-1000>];

end function;

//
// for g in GOPlus(2*l,2)
// return sequence S = [<i_1,j_1>, ..., <i_t, j_t>]
// such that g = f(i_1,j_1) * ... * f(i_t,j_t)
// here f(i,j) = D_{i,j} if 1 <= i < j <= l.
//      f(i,i) = C_i     if 1 <= i <= l.
// In other words, we have g equal to CDseqtoeltPlus(S);
CDwordPlus := function(g)

    l := #Rows(g) div 2;
 
    if l eq 1 then
	  if Order(g) eq 1 then
		return [];
	  end if;
	
	 return [<1,1>];
    end if;

	L := CDfirstpairPlus(g);
	h := g;

    // L -> L[1]*L[2]*...*L[#L] ...

    for i in [1..#L] do
	  x := L[#L-i+1];
	  if x[1] eq x[2] then
		h := CmapGO(x[1],l)*h;
	  end if;
	  if x[1] ne x[2] then
		h := DmapGO(x[1],x[2],l)*h;
	  end if;
   end for;
   
   // now h is a map such that
   // h*e_1 = e_1.
   // h*f_1 = f_1.

   gp := Submatrix(h,2,2,2*l-2,2*l-2);

   // D_{i,j} in O^+(2l-2,2) corresponds to D_{i+1,j+1} in O^+(2l,2). 
   // similarly C_i corresponds to C_{i+1} in O^+(2l,2).  
   K := [<x[1]+1,x[2]+1> : x in $$(gp)];
   
   //
   // Let a = CDseqtoeltPlus(L)
   //     b = CDseqtoeltPlus(K)
   // we have now a*g = b; so g = a^-1 * b
   // all the generators are involutions, so inverse is given simply by reversing order of the sequence.
   //
   return Reverse(L) cat K;

end function;



//
// L := [v_1, ..., v_{2*l}]
// v = (v_1, ..., v_{2l}) vector in natural module of GO^-(2l,2)
// basis of hyperbolic pairs
// e_1, ..., e_l, f_l, ..., f_1
// with Q(e_i) = Q(f_j) = 0 for 1 <= i,j <= l-1
//      Q(e_l) = Q(f_l) = 1
//      b(e_i,f_j) = 1 if i = j, and 0 otherwise.
//
// return sequence S = [<i_1,j_1>, ..., <i_t,j_t>] such that:
//
// first define x = f(i_1,j_1) ... f(i_t,j_t)
// where f(i,j) = D_{i,j} if 1 <= i < j <= l-1 and f(i,i) = C_i.
//       <0,0> = E' and <t,l> = D_t', in GO^-(2l,2).
//
// In other words x = CDseqtoeltMinus(S)
// If l > 1, then
// x*v = e_1 if Q(v) = 0.
// x*v = e_l if Q(v) = 1.
CDsequenceMinus := function(v)

	if {x : x in v} eq {0} then
		return [];
	end if;

	l := #v div 2;

    // value of Q(v)
	s := v[l] + v[l+1] + &+[ v[i]*v[2*l+1-i] : i in [1..l] ];
	
	if l eq 1 then
		c1 := v[1];
		c2 := v[2];
		
		if s eq 0 then
			return [];
		end if;
		
		if c2 eq 0 then
			return [];
		end if;
		
		if c2 eq 1 then
			if c1 eq 0 then
				return [<l,l>];
			end if;
			
			if c1 eq 1 then
				return [<l,l>, <0,0>];
			end if;
		end if;	
	end if;
	
	// v = v'+v''
	// v'  in subspace <e_1, f_1, ..., e_(l-1), f_(l-1)>
	// v'' in subspace <e_l, f_l>
	
	c := v[l];
	d := v[l+1];
	
	Lp := [v[j] : j in [1..(l-1)]] cat [v[j] : j in [l+2..(2*l)]];
    
	// case where v' = 0, or l = 1.
	if (l eq 1) or ({x : x in Lp} eq {0}) then
	
		if s eq 0 then
			return [];
		end if;
		
		if d eq 0 then
			return [];
		end if;
		
		if d eq 1 then
			if c eq 0 then
				return [<l,l>];
			end if;
			
			if c eq 1 then
				return [<l,l>, <0,0>];
			end if;
		end if;	

	end if;
	
	// for the remainder we are in a situation where l > 1, and v' is nonzero.
	
	if s eq 0 then
	
		// v'' = 0
		if (c eq 0) and (d eq 0) then
			return CDsequencePlus(Lp);
		end if;
		
		// v'' != 0, so v' is conjugate to e_1+f_1 by the following sequence g.
		g := CDsequencePlus(Lp);
		
		// v'' is conjugate to e_l by the following sequence h.
		h := [];
		if (d eq 1) then
			if c eq 0 then
				h := [<l,l>];
			end if;
			
			if c eq 1 then
				h := [<l,l>, <0,0>];
			end if;
		end if;
		
		// g cat h => e_1 + f_1 + e_l
		// C_1 D_1' (e_1+f_1+e_l) = e_1.
		
		return [<1,1>, <1,l>] cat g cat h;		
	end if;
	
	if s eq 1 then
	
		// v'' = 0
		if (c eq 0) and (d eq 0) then
			// Q(v') = 1, so this conjugates v to e_1+f_1
			g := CDsequencePlus(Lp);
			// C_l*D_1'*C_1*C_l*D_1' maps (e_1+f_1) to e_l
			return [<l,l>, <1,l>, <1,1>, <l,l>, <1,l>] cat g;
		end if;
		
		//
		// v'' != 0
		// In this case Q(v') = 0, so v' = 0 or v' conjugate to e_1.
		// (Recall case v' = 0 has been considered earlier.)
		//	
		
		g := CDsequencePlus(Lp);
		
		// C_lD_1'    (e_1+f_l)   = e_l
		// C_lD_1'C_l (e_1 + e_l) = e_l
		// C_lD_1'E'  (e_1 + e_l + f_l) = e_l
		
		if (c eq 0) and (d eq 1) then
			return [<l,l>, <1,l>] cat g;
		end if;
		
		if (c eq 1) and (d eq 0) then
		    return [<l,l>, <1,l>, <l,l>] cat g;
		end if;
	
		if (c eq 1) and (d eq 1) then
			return [<l,l>, <1,l>, <0,0>] cat g;
		end if;
	
	end if;

	// this should never happen if v is valid sequence
	return [<-1000,-1000>];

end function;

//
// conjugate pairs (v,w) with Q(v) = Q(w) = 1 and b(v,w) = 1 into
// the pair (e_l, f_l); using the generators of GOMinus(2*l,2) ...
// return sequence as usual
CDfirstpairMinus := function(g)

	l := #Rows(g) div 2;

	// Case-by-case for the 6 matrices in O_2^{-}(2).
	if l eq 1 then

	// [1 0]
	// [0 1]
		if Order(g) eq 1 then
			return [];
		end if;
		
		if Order(g) eq 2 then
			// [0 1]
			// [1 0] = C_1
			if g[1][1] eq 0 and g[2][2] eq 0 then
				return [<1,1>];
			end if;
			
			if g[1][1] eq 1 and g[2][2] eq 1 then
				// [1 1]
				// [0 1] = E'			
				if g[2][1] eq 0 then
				return [<0,0>];
				end if;
				
				// [1 0]
				// [1 1] = C_1E'C_1	
				if g[1][2] eq 0 then
				return [<1,1>, <0,0>, <1,1>];
				end if;
				
			end if;
			
		end if;
		
		if Order(g) eq 3 then
			// [1 1]
			// [1 0] = E'C_1	
			if g[1][1] eq 1 then
				//return [<0,0>, <1,1>];
				return [<1,1>, <0,0>];
			end if;
			
			// [0 1]
			// [1 1] = C_1E'			
			if g[1][1] eq 0 then
				return [<0,0>, <1,1>];
				//return [<1,1>, <0,0>];
			end if;
		end if;
		
		// this should never happen
		return [<-1000,-1000>];
	end if;

	v := Transpose(g)[l];
	v := [v[j] : j in [1..#Rows(g)]];

	L := CDsequenceMinus(v);
	h := g;

	// L -> L[1]*L[2]*...*L[#L] ...

	for i in [1..#L] do
		x := L[#L-i+1];

		if x[1] eq x[2] then
			if x[1] ne 0 then
			h := CmapGO(x[1],l)*h;
			end if;
			if x[1] eq 0 then
			h := EmapGO(l)*h;
			end if;
		end if;
		
		if x[1] ne x[2] then
			if x[2] lt l then
			h := DmapGO(x[1],x[2],l)*h;
			end if;
			if x[2] eq l then
			h := DmapminusGO(x[1],l)*h;
			end if;
		end if;
		
	end for;
		

	c := h[l][l+1];
	w := [h[j][l+1] : j in [1..(l-1)] cat [(l+2)..(2*l)]];

	if {x : x in w} eq {0} then
		if c eq 0 then
			return L;
		end if;
		
		if c eq 1 then
			return [<0,0>] cat L;
		end if;
	end if;

	K := CDsequencePlus(w);

	if c eq 0 then
		return [<1,l>] cat K cat L;
	end if;

	if c eq 1 then
		return [<1,l>, <0,0>] cat K cat L;
	end if;

	return [<-1000,-1000>];

end function;



// for g in GOMinus(2*l,2)
// return sequence [<i_1,j_1>, ..., <i_t, j_t>]
// such that g = f(i_1,j_1) * ... * f(i_t,j_t)
// here f(i,j) = D_{i,j} if 1 <= i < j <= l-1.   DmapGO(i,j,l);
//      f(i,l) = D_i'    if 1 <= i <= l-1.       DmapminusGO(i,l);
//      f(i,i) = C_i     if 1 <= i <= l.         CmapGO(i,l);
//      f(0,0) = E'                              EmapGO(l);
CDwordMinus := function(g)

    l := #Rows(g) div 2;
 
    if l eq 1 then
	  L := CDfirstpairMinus(g);
	  return Reverse(L);
    end if;

	L := CDfirstpairMinus(g);
	h := g;

    // L -> L[1]*L[2]*...*L[#L] ...

    for i in [1..#L] do
	x := L[#L-i+1];

	if x[1] eq x[2] then
		if x[1] ne 0 then
		h := CmapGO(x[1],l)*h;
		end if;
		if x[1] eq 0 then
		  h := EmapGO(l)*h;
		end if;
	end if;
	
	if x[1] ne x[2] then
		if x[2] lt l then
		  h := DmapGO(x[1],x[2],l)*h;
		end if;
		if x[2] eq l then
		  h := DmapminusGO(x[1],l)*h;
		end if;
	end if;
	
	end for;
   
   gp := h;
   gp := RemoveRow(gp,l+1);
   gp := RemoveRow(gp,l);
   gp := RemoveColumn(gp,l+1);
   gp := RemoveColumn(gp,l);

   
   u := CDwordPlus(gp);
   
   return Reverse(L) cat u;
   
end function;



// generators for Sp(2l,r) for r odd prime

// C_t for 1 <= t <= l in Sp(2l,r)
// e_t -> -f_t
// f_t -> e_t
CmapSP := function(t,l,r)
 return 1+Matrix(GF(r), 2*l,2*l, [<t,2*l+1-t,1>, <2*l+1-t,t,-1>, <t,t,-1>, <2*l+1-t, 2*l+1-t,-1>]); 
end function;

// D_st (for 1 <= s < t <= l) in Sp(2l,r)
// f_t -> f_t + e_s
// f_s -> f_s + e_t
DmapSP := function(s,t,l,r)
 return 1+Matrix(GF(r), 2*l,2*l, [<s,2*l+1-t,1>, <t,2*l+1-s,1>]);
end function;

// E_t for 1 <= t <= l in Sp(2l,r)
// f_t -> f_t + e_t
EmapSP := function(t,l,r)
 return 1+Matrix(GF(r),2*l,2*l,[<t,2*l+1-t,1>]);
end function;

//
// For element g of SL(2,r) = Sp(2,r) (r prime)
// 
//     [a b]
// g = [c d]
//
// this function returns c1,c2,c3,c4 such that
// g = y^c1 * x^c2 * y^c3 * x^c4
//
// where x and y are standard transvections 
//
//     [1 1]           [1 0]
// x = [0 1]       y = [1 1]
//
sp2word := function(g)

	r := Characteristic(BaseRing(g));

	a := g[1][1];
    b := g[1][2];
    c := g[2][1];
    d := g[2][2];

    c1 := 0;
    c2 := 0;
    c3 := 0;
    c4 := 0;

    if c ne 0 then
     c1 := IntegerRing()!0;
     c2 := IntegerRing()!(a * (1-d)/c + b);
     c3 := IntegerRing()!c;
     c4 := IntegerRing()!((d-1)/c);
    end if;

    if c eq 0 then
     c1 := IntegerRing()!(-1);
     c2 := IntegerRing()!(1-d);
     c3 := IntegerRing()!a;
     c4 := IntegerRing()!((b+d-1)/a);
    end if;
	
	return c1,c2,c3,c4;
	
end function;

// <t,0,x> = E_t^x
// <0,t,x> = C_t^x
// <s,t,x> = D_{st}^x
CDEseqtoelt := function(L,l,r)
    g := Sp(2*l,r)!1;

    for x in L do
        // <0,t,x> = C_t^x
        if x[1] eq 0 then
            g := g*CmapSP(x[2], l, r)^x[3];
        // <t,0,x> = E_t^x
        elif x[2] eq 0 then
            g := g*EmapSP(x[1], l, r)^x[3];
        // <s,t,x> = D_st^x
        else
            g := g*DmapSP(x[1], x[2], l, r)^x[3];
        end if;
    end for;

    return g;
end function;

CDseqtoeltPlus := function(L,l)
	g := GOPlus(2*l,2)!1;

	for x in L do
		if x[1] eq x[2] then
			g := g*CmapGO(x[1],l);
		else
			g := g*DmapGO(x[1],x[2],l);
		end if;
	end for;

	return g;
end function;

CDseqtoeltMinus := function(L,l)
	g := GOMinus(2*l,2)!1;

	for x in L do
		if x[1] eq x[2] then

			if x[1] ne 0 then
			g := g*CmapGO(x[1],l);
			end if;
			if x[1] eq 0 then
			g := g*EmapGO(l);
			end if;

		elif x[1] ne x[2] then

			if x[2] lt l then
			g := g*DmapGO(x[1],x[2],l);
			end if;
			if x[2] eq l then
			g := g*DmapminusGO(x[1],l);
			end if;

		end if;
	end for;

	return g;
end function;

//
//
// given a nonzero vector v in GF(r)^(2l) as a list
// v = [a_1, ..., a_{2l}];
// find product of generators that maps v to e_1.
// (Transitivity of Sp(2l,r) on non-zero vectors.)
//
// representation:
// C_t; 1 <= t <= l      : <0,t>
// E_t; 1 <= t <= l      : <t,0>
// D_st; 1 <= s < t <= l : <s,t>
//
// F_t := C_t E_t^-1 C_t^-1
// Then F_t maps e_t -> e_t + f_t; fixes other basis vectors.
//
// e.g. for     [0  1]        [1 1]         [1 0]
//          C = [-1 0]    E = [0 1]     F = [1 1]
//
//  we have C*E^-1*C^-1 = F.
//
// Notation for tuples:
// <t,0,x> = E_t^x
// <0,t,x> = C_t^x
// <s,t,x> = D_{st}^x
// Thus:
// <0,1,1>, <t,0,-x>, <0,1,-1> = F_t^x
//
CDEsequenceSP :=  function(v)

    if {x : x in v} eq {0} then
		return [];
	end if;

    l := #v div 2;

    c := v[1];
	d := v[#v];
	
    if l eq 1 then
        r := Characteristic(Parent(c));
        g := Sp(2,r)!1;

        if c ne 0 then
            g := Matrix(GF(r), 2, 2, [c, 0, d, c^-1]);
        else
            g := Matrix(GF(r), 2, 2, [0, -d^-1, d, 0]);
        end if;

        c1,c2,c3,c4 := sp2word(g);
        L := [];

        // F^c1
        if c1 ne 0 then
         L := L cat [<0,1,1>, <1,0,-c1>, <0,1,-1>];
        end if;

        // E^c2
        if c2 ne 0 then
         L := L cat [<1,0,c2>];
        end if;

        // F^c3
        if c3 ne 0 then
         L := L cat [<0,1,1>, <1,0,-c3>, <0,1,-1>];
        end if;
        
        // E^c4
        if c4 ne 0 then
         L := L cat [<1,0,c4>];
        end if;

        // L gives s.t. ge_1 = v, so let's invert the list
        L := Reverse(L);
        for i in [1..#L] do
            x := L[i];
            L[i] := <x[1],x[2],-x[3]>;
        end for;

        // g = F^c1 * E^c2 * F^c3 * E^c4 ....
        return L;
    end if;

    //
    // write v = v' + v''.
    // where v' in <e_1, f_1>.
    // v'' in <e_2,f_2, ..., e_l, f_l>.
    //
	Lp := [v[j] : j in [2..(#v-1)]];

    // case where v'' = 0; get result from [c,d].
    if {x : x in Lp} eq {0} then
        return $$([c,d]);
    end if;

    K := $$(Lp);
    // adjust indices in K to fit desired l.
    for i in [1..#K] do
        x := K[i];
        if x[1] eq 0 then
            K[i] := <0,x[2]+1,x[3]>;
        elif x[2] eq 0 then
            K[i] := <x[1]+1,0,x[3]>;
        else
            K[i] := <x[1]+1,x[2]+1,x[3]>;
        end if;
    end for;

    // case where v' = 0.
    if (c eq 0) and (d eq 0) then

        // K maps v'' to e_2.
        // C_1 * D12^-1 * C_2 * C_1^-1 * D12 * C2^-1 maps e_2 to e_1.
        // 
        L := [<0,1,1>, <1,2,-1>, <0,2,1>, <0,1,-1>, <1,2,1>, <0,2,-1>];
        //     C_1     D_12^-1     C_2     C_1^-1     D_12    C_2^-1
        return L cat K;
    end if;

    // remaining case: both v' and v'' nonzero.
    // first conjugate v' to e_1, and v'' to e_2.
    // v = e_1 + e_2.
    // C_1 D_12^-1 C_1^-1 v = e_1.

    L := [<0,1,1>, <1,2,-1>, <0,1,-1>];
    //      C_1     D_12^-1   C_1^-1
    La := $$([c,d]);
    return L cat La cat K;

end function;

// for g in Sp(2l,r)
// return sequence such that for the corresponding element h;
// hge_1 = e_1 and hgf_1 = f_1.
// i.e. can use this to conjugate hyperbolic pairs (v,w) into (e_1,f_1).
CDEfirstpairSP := function(g)

	l := #Rows(g) div 2;
	r := Characteristic(BaseRing(g));

	if l eq 1 then
		c1,c2,c3,c4 := sp2word(g);
		L := [];

		// F^c1
		if c1 ne 0 then
			L := L cat [<0,1,1>, <1,0,-c1>, <0,1,-1>];
		end if;

		// E^c2
		if c2 ne 0 then
			L := L cat [<1,0,c2>];
		end if;

		// F^c3
		if c3 ne 0 then
			L := L cat [<0,1,1>, <1,0,-c3>, <0,1,-1>];
		end if;
			
		// E^c4
		if c4 ne 0 then
			L := L cat [<1,0,c4>];
		end if;

		// g = F^c1 * E^c2 * F^c3 * E^c4 ....
		// Invert the list to get desired result
		L := Reverse(L);
		for i in [1..#L] do
				x := L[i];
				L[i] := <x[1],x[2],-x[3]>;
		end for;
		
		return L;
	end if;

	// for the remainder, we have l > 1.

	v := Transpose(g)[1];
	v := [v[j] : j in [1..#Rows(g)]];

	L := CDEsequenceSP(v);
	h := CDEseqtoelt(L,l,r) * g;

	// he_1 = e_1
	// he_n = w = c e_1 + f_1 + v''
	// find additional such that (e_1,w) mapped to (e_1,f_1).

	c := h[1][2*l];

	// E_1^-c * (c e_1 + f_1) = f_1.
	if c ne 0 then
		L := [<1,0,IntegerRing()!(-c)>] cat L;
	end if;

	w := [h[j][2*l] : j in [2..(2*l-1)]];

	// if v'' = 0, we are done
	if {x : x in w} eq {0} then
		return L;
	end if;

	// this will map v'' to e_2.
	K := CDEsequenceSP(w);
	// adjust indices in K to fit desired l.
	for i in [1..#K] do
		x := K[i];
		if x[1] eq 0 then
			K[i] := <0,x[2]+1,x[3]>;
		elif x[2] eq 0 then
			K[i] := <x[1]+1,0,x[3]>;
		else
			K[i] := <x[1]+1,x[2]+1,x[3]>;
		end if;
	end for;

	// D_12^-1 maps (e_1,f_1+e_2) to (e_1, f_1).

	return [<1,2,-1>] cat K cat L;

end function;

//
// g = element of Sp(2l,r), where r is a prime.
// return sequence corresponding to g.
CDEwordSP := function(g)

	l := #Rows(g) div 2;
	r := Characteristic(BaseRing(g));

	if l eq 1 then
		c1,c2,c3,c4 := sp2word(g);
		L := [];

		// F^c1
		if c1 ne 0 then
			L := L cat [<0,1,1>, <1,0,-c1>, <0,1,-1>];
		end if;

		// E^c2
		if c2 ne 0 then
			L := L cat [<1,0,c2>];
		end if;

		// F^c3
		if c3 ne 0 then
			L := L cat [<0,1,1>, <1,0,-c3>, <0,1,-1>];
		end if;
			
		// E^c4
		if c4 ne 0 then
			L := L cat [<1,0,c4>];
		end if;
		
		return L;
	end if;

	L := CDEfirstpairSP(g);
	h := CDEseqtoelt(L,l,r) * g;

	gp := Submatrix(h,2,2,2*l-2,2*l-2);

	K := $$(gp);
	// adjust indices in K to fit desired l.
	for i in [1..#K] do
		x := K[i];
		if x[1] eq 0 then
			K[i] := <0,x[2]+1,x[3]>;
		elif x[2] eq 0 then
			K[i] := <x[1]+1,0,x[3]>;
		else
			K[i] := <x[1]+1,x[2]+1,x[3]>;
		end if;
	end for;

	// invert L
	L := Reverse(L);
	for i in [1..#L] do
				x := L[i];
				L[i] := <x[1],x[2],-x[3]>;
	end for;

	return L cat K;

end function;

wordminimizerMinus := procedure(H)
	K := sub<H|1>;
	R := [];
	L := [];
	wordfunc := CDwordMinus;
	while K ne H do
		best := 9999;
		best_elt := H!1;
		best_L := [];
		for x in H do
			if x notin K then
				c := wordfunc(x);
				if #c lt best then
					best := #c;
					best_L := c;
					best_elt := x;
				end if;
			end if;
		end for;

		R := R cat [best_elt];
		L := L cat [best_L];
		K := sub<H|K,best_elt>;
	end while;

	print "";
	print "Result: ",#L,"generators";
	print "Word lengths:",[#wordfunc(x) : x in R];
	print "Words:";
	print L;
	print "";

end procedure;

wordminimizerPlus := procedure(H)
	K := sub<H|1>;
	R := [];
	L := [];
	wordfunc := CDwordPlus;
	while K ne H do
		best := 9999;
		best_elt := H!1;
		best_L := [];
		for x in H do
			if x notin K then
				c := wordfunc(x);
				if #c lt best then
					best := #c;
					best_L := c;
					best_elt := x;
				end if;
			end if;
		end for;

		R := R cat [best_elt];
		L := L cat [best_L];
		K := sub<H|K,best_elt>;
	end while;

	print "";
	print "Result: ",#L,"generators";
	print "Word lengths:",[#wordfunc(x) : x in R];
	print "Words:";
	print L;
	print "";

end procedure;

