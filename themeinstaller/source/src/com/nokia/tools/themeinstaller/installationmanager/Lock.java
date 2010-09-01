/*
* Copyright (c) 2007 Nokia Corporation and/or its subsidiary(-ies). 
* All rights reserved.
* This component and the accompanying materials are made available
* under the terms of "Eclipse Public License v1.0"
* which accompanies this distribution, and is available
* at the URL "http://www.eclipse.org/legal/epl-v10.html".
*
* Initial Contributors:
* Nokia Corporation - initial contribution.
*
* Contributors:
*
* Description:  Helper class for waiting asynchronous operations.
 *
*/


package com.nokia.tools.themeinstaller.installationmanager;

/**
 * Helper class for waiting asynchronous operations.
 */
public class Lock
    {

    private boolean iNotify = false;

    /*
     * Calls wait() if unLock() hasn't been called.
     * Causes thread to wait until unLock() is called.
     */
    synchronized public void lock()
        {
        if( !iNotify )
            {
            try
                {
                wait();
                }
            catch ( InterruptedException e )
                {
                //ignore
                }
            }
        iNotify = false;
        }

    /*
     * Called when asynchronous operation is ready.
     * Wakes up a thread that is waiting on this object's monitor.
     */
    synchronized public void unLock()
        {
        iNotify = true;
        notify();
        }
    }
