USING: accessors kernel kernel.private mm9 ! mm9.single 
namespaces quotations
sequences words ;
QUALIFIED-WITH: generic.single.private gsp
IN: mm9.hook

PREDICATE: single-hook-generic < multi-generic
    "dispatch-type" word-prop single-hook-dispatch? ;

M: single-hook-dispatch [picker]
    dispatch-type get var>> [ get ] curry ;

M: single-hook-dispatch single-dispatch# drop 0 ;

M: single-hook-dispatch mega-cache-quot
    1quotation [picker] [ gsp:lookup-method (execute) ] surround ;

M: single-hook-generic effective-method
    [ "dispatch-type" word-prop var>> get ] keep method-for-object ;


