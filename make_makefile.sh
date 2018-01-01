#!/bin/sh

#coq_makefile -R "." HSLib -o makefile Base.v Alternative/**v Applicative Functor Instances InstancesT MonadBind MonadComp MonadJoin MonadPlus MonadTrans

coq_makefile -R "." HSLib -o makefile **v */**v

#coq_makefile -R "." RandomCoqCode -o makefile RCCBase.v Reflection/**v Sorting/**v Structures/**v Trash/**v Trees/**v
