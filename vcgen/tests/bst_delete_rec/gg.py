Final alloc set:  SPKeys0(x0)


Sp of postcondition: SPKeys0(x0) U SPKeys1(ret0)

Lemma : ((x0,), SPKeys1(x0) == SPbst1(x0))
Lemma : ((x0,), SPKeys0(x0) == SPbst0(x0))

goal:-> Implies(And(
            And(bst0(x0), Keys0(x0)[k0]),
            key0(x0) == k0,
            head1 == x0,
            lft0 == left0(x0),
            rgt0 == right0(x0),

            And(bst1(ret0),
                Keys1(ret0) ==
                union(Keys0(lft0), Keys0(rgt0)))
                
                ),

        And(bst1(ret0),
            Store(Keys1(ret0), k0, True) == Keys0(x0))
            
            )

INFO:root:Adding support of recdef: (SPKeys1, [x0], If(x0 == nil,
   K(Int, False),
   Map(or,
       K(Int, False),
       Map(or,
           Map(or,
               Store(K(Int, False), x0, True),
               SPKeys1(left1(x0))),
           SPKeys1(right1(x0))))) )























           INFO:root:Final alloc set: 

                        
                                SPLseg0(head0, x0), x0, SPList0(y0), SPKeys0(y0), SPKeys0(x0), SPKeys0(head0), SPKeyseg0(head0, x0), SPList0(x0)


INFO:root:Sp of postcondition: 
SPList1(ret1),
            SPKeys0(head0)),
        SPKeys0(y0)),
    SPKeys1(ret1))