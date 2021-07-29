/* Proc
 * Author: Veronica
 * Creation date: 2021/4/18
 */
MACHINE
    Proc
DEFINITIONS
scope_Proc ==1
SETS
PROC;MODE = {NU ,NS,TU,TS,MM};
EXE_STATE = {Ready,Run,Blocked,Final};
AC_STATE = {Pre,Wait,Acing,Post}
VARIABLES
proc,PID,pid,pmode,exe_state,ac_state,proc_mpu
INVARIANT
proc ⊆ PROC ∧
PID ⊆ NAT1 ∧
pid ∈ proc → PID ∧
pmode ∈ proc → MODE ∧
exe_state ∈ proc → EXE_STATE ∧  //the status of processes
ac_state ∈ proc → AC_STATE ∧ 
proc_mpu ∈ proc ↣ 0..7 
INITIALISATION
proc,PID,pid,pmode,exe_state,/*proc_dom,*/ac_state,proc_mpu := {},{},{},{},{},{},{}
OPERATIONS    
    Create_Proc(pp,ii,ex,ac,mpu) =
    PRE
           pp ∈ PROC ∧
           pp ∉ proc ∧
		ii ∈ NAT1 ∧
		ii ∉ PID ∧
           ex = Ready ∧
	   ac = Pre ∧ 
           mpu ∈ 0..7 ∧
           pp |-> mpu ∉ proc_mpu ∧
	   card(proc_mpu)<8 ∧
		mpu ∉ ran(proc_mpu)
    THEN
           proc := proc ∪ {pp} ||
		PID := PID ∪ {ii} ||
		pid(pp) := ii ||
		pmode(pp) :=  NU ||
           exe_state := exe_state ∪ {pp|->ex} ||
	   ac_state := ac_state ∪ {pp|->ac} ||
           proc_mpu := proc_mpu ∪ {pp |-> mpu} 
    END;
    
    Del_Proc(pp) =
    PRE
        pp : proc
    THEN
        proc := proc - {pp} ||
	PID := PID - {pid(pp)}||
	pid := {pp} ◀ pid ||
	pmode := {pp} ◀ pmode ||
	ac_state := {pp} ◀ ac_state ||
        exe_state := {pp} ◀ exe_state ||
        proc_mpu := {pp} ◀ proc_mpu 
    END;
	Change_Proc_State(pp,ex,ac)=
	PRE
		pp ∈ proc &
		ex ∈ EXE_STATE &
		ac ∈ AC_STATE
	THEN
		exe_state(pp) := ex ||
		ac_state(pp) := ac
	END;
	Change_Proc_Mode(pp,dd) =
	PRE
		pp ∈ proc &
		dd ∈ MODE
	THEN
		pmode(pp) :=  dd
	END   
END
