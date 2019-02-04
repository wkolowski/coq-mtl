#!/bin/sh

#coq_makefile -R "." HSLib -o makefile **v */**v

coq_makefile -R "." HSLib -o makefile *v */*v */*/*v */*/*/*v 
#Control/*v Instances/*v InstancesT/*v Misc/*v MonadClass/*v Parser/*v Tactics/*v Theory/*v Theory/Laws/*v Theory/Equivs/*v
