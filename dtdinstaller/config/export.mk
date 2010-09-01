#
# Copyright (c) 2009 Nokia Corporation and/or its subsidiary(-ies).
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
# dtdinstaller's actual configuration export makefile

MAKEFILE =	/sf/app/homescreentools/dtdinstaller/config/export.mk
$(call push,MAKEFILE_STACK,$(MAKEFILE))

DTDINSTALLERFILES =	$(MAKEFILEDIR)../bin/dtd_installer.pl													/epoc32/tools/ \
													$(MAKEFILEDIR)../bin/convert_file.pm										/epoc32/tools/ \
													$(MAKEFILEDIR)../bin/dtd.meta														/epoc32/tools/makefile_templates/tools/ \
													$(MAKEFILEDIR)../bin/dtd.mk															/epoc32/tools/makefile_templates/tools/

dtdinstaller_config								:: dtdinstaller_config-dtdinstaller 
dtdinstaller_config-dtdinstaller	::

$(call addfiles, $(DTDINSTALLERFILES), dtdinstaller_config-dtdinstaller)

$(call popout,MAKEFILE_STACK)