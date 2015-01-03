#include <stdlib.h>
#include "vpi_user.h"
#include "vpi_user_cds.h"

#include "pli.h"
#include "controls.h"

// Format is (vpiSysTask/Func, 0, $VpiFuncName, CFuncName,0,0,0)

// Documentation
//typedef struct t_vpi_systf_data
//{
// PLI_INT32 type; /* vpiSysTask, vpiSysFunc */
//  PLI_INT32 sysfunctype; /* vpiSysTask, vpi[Int,Real,Time,Sized,
//			    SizedSigned]Func */
//  PLI_BYTE8 *tfname; /* first character must be `$' */
//  PLI_INT32 (*calltf)(PLI_BYTE8 *);
//  PLI_INT32 (*compiletf)(PLI_BYTE8 *);
//  PLI_INT32 (*sizetf)(PLI_BYTE8 *); /* for sized function
//				       callbacks only */
//  PLI_BYTE8 *user_data;
//} s_vpi_systf_data, *p_vpi_systf_data;
#define VPI_SYSTASK(name) {vpiSysTask, vpiSysTask, "$" #name, name, NULL, NULL, NULL}
// FIXME on this: it's not giving any function info!
#define VPI_SYSFUNC(name) {vpiSysFunc, 0, "$" #name, name, NULL, NULL, NULL}

static s_vpi_systf_data systfList[] = {
  // SysFuncs
  VPI_SYSFUNC(load_mm),
  VPI_SYSFUNC(load_next_test),
  VPI_SYSFUNC(emulate_syscall),
  VPI_SYSFUNC(syscall_getreg),
  VPI_SYSFUNC(syscall_getpc),
  VPI_SYSFUNC(icache_tag_read),
  VPI_SYSFUNC(icache_state_read),
  VPI_SYSFUNC(icache_data_read),
  VPI_SYSFUNC(dcache_tag_read),
  VPI_SYSFUNC(dcache_state_read),
  VPI_SYSFUNC(dcache_data_read),
  VPI_SYSFUNC(scache_tag_read),
  VPI_SYSFUNC(scache_state_read),
  VPI_SYSFUNC(scache_data_read),
  
  // SysTasks
  VPI_SYSTASK(get_value),
  VPI_SYSTASK(seed_mm),
  VPI_SYSTASK(seed_mm_test),
  VPI_SYSTASK(store_mm),
  VPI_SYSTASK(disasm),
  VPI_SYSTASK(syscall_setreg),
  VPI_SYSTASK(syscall_setpc),
  VPI_SYSTASK(create_icache),
  VPI_SYSTASK(create_dcache),
  VPI_SYSTASK(create_scache),
  VPI_SYSTASK(icache_tag_write),
  VPI_SYSTASK(icache_state_write),
  VPI_SYSTASK(icache_data_write),
  VPI_SYSTASK(dcache_tag_write),
  VPI_SYSTASK(dcache_state_write),
  VPI_SYSTASK(dcache_data_write),
  VPI_SYSTASK(scache_tag_write),
  VPI_SYSTASK(scache_state_write),
  VPI_SYSTASK(scache_data_write),
  {0},
};

//void seed_mm_register()
//{
//  s_vpi_systf_data tf_data;
//
//  tf_data.type = vpiSysTask;
//  tf_data.sysfunctype = 0;
//  tf_data.tfname = "$seed_mm";
//  tf_data.calltf = seed_mm;
// tf_data.compiletf = 0;
//  tf_data.sizetf = NULL;
//  tf_data.user_data = NULL;

//  vpi_register_systf(&tf_data);
  //  vpi_printf("I am being called");
//}




// Register all the VPI callbacks.
void register_vpi_callbacks()
{
  //printf("I am registering callbacks now\n");
  p_vpi_systf_data systf_data_p = &(systfList[0]);
  while (systf_data_p->type)
    {
      vpi_register_systf(systf_data_p++);
      //printf("callback registered: %s\n", systf_data_p->tfname);
    }
}

// This is a list of functions to call on startup.
void (*vlog_startup_routines[])() =
{
  register_vpi_callbacks,
  0 /*** final entry must be 0 ***/
};

