# Cash machine

A PCs description of a cash machine made-up of several constituent PCs:
* <i>PC_CashMachine</i> gives overall description, saying that <i>CashMachine</i> is a process which keeps running. <i>CashMachine</i> puts together <i>CardControl</i> and another throw operator 
using a parallel composition operator which synchronises on events <i>deny</i>, <i>cardIn</i> and <i>cancel</i>.
* <i>PC_CardControl</i> provides a
* <i>PC_Authentication</i> describes authentication through a number of tries (parameter <i>n</i>).
If there are no tries left, then event <i>deny</i> happens as authentication failed. If there are tries left then authentication may either be successful (<i>grant</i>) or simply <i>fail</i>, in which case a user may have another try, if there are tries left.
