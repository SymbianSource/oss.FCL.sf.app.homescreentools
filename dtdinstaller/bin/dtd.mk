#
# Copyright (c) 2008 Nokia Corporation and/or its subsidiary(-ies).
# All rights reserved.
# This component and the accompanying materials are made available
# under the terms of "Eclipse Public License v1.0"
# which accompanies this distribution, and is available
# at the URL "http://www.eclipse.org/legal/epl-v10.html".
#
# Initial Contributors:
# Nokia Corporation - initial contribution.
#
# Contributors:
#
# Description:
#

# To ensure that EPOCROOT always ends with a forward slash
TMPROOT:=$(subst \,/,$(EPOCROOT))
EPOCROOT:=$(patsubst %/,%,$(TMPROOT))/

ifndef SWITCH_LOC_FILE_NAME
$(error switch loc file unknown)
endif

DTD_INSTALLER_TOOL := perl $(EPOCROOT)epoc32/tools/dtd_installer.pl

ifdef SWITCH_LOC_FILE_PATH
SWITCH_LOC_FILE_PATH := $(EPOCROOT)$(SWITCH_LOC_FILE_PATH)
endif

# default type is dtd (Theme installer is not called, only loc_to_dtd_converter.pl !)
ifndef DTD_TYPE
  DTD_TYPE := dtd
endif


ifeq ($(DTD_TYPE),widget)
  ifndef DTD_PRIVATE_LOCATION
    DTD_PRIVATE_LOCATION := z/private/200159c0/install
  endif
  ifeq ($(PLATFORM),WINSCW)
        PRODUCTIZATION_LOCATION := $(EPOCROOT)epoc32/release/winscw/$(CFG)/$(DTD_PRIVATE_LOCATION)
  endif
  ifeq ($(PLATFORM),ARMV5)
  		PRODUCTIZATION_LOCATION := $(EPOCROOT)epoc32/data/$(DTD_PRIVATE_LOCATION)
  endif
else # Type is DTD by default
  ifndef DTD_PRIVATE_LOCATION
    DTD_PRIVATE_LOCATION := z/private/200113DD/content
  endif
  ifeq ($(PLATFORM),WINSCW)
        PRODUCTIZATION_LOCATION := $(EPOCROOT)epoc32/release/winscw/$(CFG)/$(DTD_PRIVATE_LOCATION)
  endif
  ifeq ($(PLATFORM),ARMV5)
  		PRODUCTIZATION_LOCATION := $(EPOCROOT)epoc32/data/$(DTD_PRIVATE_LOCATION)
  endif
endif

ifndef DTD_OUTPUT_LOCATION
  DTD_OUTPUT_LOCATION := $(PRODUCTIZATION_LOCATION)
else 
  DTD_OUTPUT_LOCATION := $(EPOCROOT)$(DTD_OUTPUT_LOCATION)
endif 

DTD_INSTALLER_TOOL := $(DTD_INSTALLER_TOOL) -o $(DTD_OUTPUT_LOCATION) -n $(SWITCH_LOC_FILE_NAME) -t $(DTD_TYPE)

ifdef LOC_FOLDERS
	DTD_INSTALLER_TOOL := $(DTD_INSTALLER_TOOL) -f force
endif

ifdef DEBUG_MODE
	DTD_INSTALLER_TOOL := $(DTD_INSTALLER_TOOL) -d yes
endif

DTD_INSTALLER_TOOL_BUILD := $(DTD_INSTALLER_TOOL) -a build
DTD_INSTALLER_TOOL_CLEAN := $(DTD_INSTALLER_TOOL) -a clean
DTD_INSTALLER_TOOL_WHAT := $(DTD_INSTALLER_TOOL) -a what

#OUTPUT_PATH

# DTD tool will be invoked here
DO_DTD_BUILD:
	$(DTD_INSTALLER_TOOL_BUILD)
DO_DTD_CLEAN:	
	$(DTD_INSTALLER_TOOL_CLEAN)
DO_DTD_WHAT:	
	$(DTD_INSTALLER_TOOL_WHAT)

	
BLD SAVESPACE: DO_NOTHING
CLEAN : DO_DTD_CLEAN
RELEASABLES :	DO_DTD_WHAT
	
DO_NOTHING :
	@echo do nothing
	
MAKMAKE : 
FREEZE : DO_NOTHING
LIB : DO_NOTHING
CLEANLIB : DO_NOTHING
RESOURCE : DO_DTD_BUILD
FINAL : DO_NOTHING

FINAL FREEZE LIB CLEANLIB RESOURCE RELEASABLES CLEAN BLD SAVESPACE MAKMAKE :



