new method:

baseline: either () or blank space = invisible ()
    - baseline has *ONLY ONE* equation. that equation will always has lv=0;
    - this hold the real lv, so equations of this baseline will be calculated at the end
    - min lv = 0;
equation: hold expressions
    - hold variable and children expressions(clauses) as literal
    - AND, OR
    - first encounter operator will always has lv=0;
        - if meet OR first, 
            add AND or () = lv++;
        - if meet AND first,
            AND = 1;
                loop all val to update lv of children ()
            OR = 0;
baseline and equation are both the same type=ExpressionInfo
after finishing the search. use recursion to assign lv from root


                                          Z&X
                                ------------------------
                                holdChild = &
                                baselineVVV
                                           ^
                                           |
                                           |
                A&B                     C&( )
                              ()|()
                              baselineVVV

baseline---------------------------------------------------------
holdChild = |
                                ^
                                |
                                |
                            A&B|C&(Z&X)




A&(B&(C&(D&(E&(F&(G&H|I)|J)|K)|L)|M)|N)|O

B&((((A))))
B&((((A)&C|D)))

