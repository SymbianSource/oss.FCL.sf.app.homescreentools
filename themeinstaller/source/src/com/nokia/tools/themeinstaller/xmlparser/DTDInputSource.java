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
* Description:  File Reader for DTD Files. Filters out UTF-8 and 16 byte order
 *                marks.
 *
*/


package com.nokia.tools.themeinstaller.xmlparser;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;
import java.util.Arrays;

import org.xml.sax.InputSource;

import com.nokia.tools.themeinstaller.installationmanager.InstallationManager;

/**
 * File Reader for DTD Files. Filters out UTF-8 and 16 byte order marks. Byte
 * order marks need to be filtered because FileReader can not tolerate BOMs.
 */
public class DTDInputSource extends InputSource {

	// CONSTANTS
	private final static int BUFFER_LENGTH = 3;
	private final static byte[] BOM_UTF8 = { (byte) 0xEF, (byte) 0xBB,
			(byte) 0xBF };
	private final static byte[] BOM_UTF16_BIG = { (byte) 0xFE, (byte) 0xFF };
	private final static byte[] BOM_UTF16_LIT = { (byte) 0xFF, (byte) 0xFE };

	// DTD File name
	private String iFileName;

	/**
	 * Constructor.
	 * 
	 * @param aFileName
	 *            DTD file name
	 * @throws FileNotFoundException
	 *             if the file can not be found
	 */
	public DTDInputSource(String aFileName) throws FileNotFoundException {
		super( new FileReader( aFileName ) );
		try {
			preprocess(aFileName);
		} catch (IOException e) {			
			e.printStackTrace();
		}
		iFileName = aFileName;
	}

	/**
	 * XML-DTD files should not contain invalid entity references. For example,
	 * %N; is valid while %N is not. This method will validate and correct such
	 * instances. Note: This was introduced because of a defect found in loc to
	 * dtd converter tool. Once loc-dtd tool works fine, this step will not be
	 * required.
	 * 
	 * @param fileName
	 *            the dtd file that needs correction.
	 * @throws IOException
	 */
	private void preprocess(String fileName) throws IOException {

		
		/**
		 * We won't use this parameter as of now. If required, use
		 * boolean fixDTD = InstallationManager.isFixDTD();
		 * We may remove this if we find no use in future.
		 */
		boolean fixDTD = true;
		if (!fixDTD) {
			this.setCharacterStream(new FileReader(fileName));
			return;
		}
		long fileLen = (new File(fileName)).length();
		byte[] fileContents = new byte[(int) fileLen];
		FileInputStream fis = new FileInputStream(fileName);
		fis.read(fileContents);
		fis.close();

		String fileContentsString = new String(fileContents);
		fileContentsString = fileContentsString.replace("(%N)", "(%N;)");
		fileContentsString = fileContentsString.replace("(%U)", " (%U;)");
		fileContentsString = fileContentsString.replace("%0U;", "%U;");
		fileContentsString = fileContentsString.replace("%U(", "%U;(");
		fileContentsString = fileContentsString.replace("%0U(", "%U;(");
		fileContentsString = fileContentsString.replace("%U%N;", "%U;%N;");
		fileContentsString = fileContentsString.replace("%U%N", "%U;%N;");

		setByteStream(new ByteArrayInputStream(fileContentsString.getBytes()));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.xml.sax.InputSource#getCharacterStream()
	 */
	public Reader getCharacterStream() {
		// Get the reader from the base class
		Reader reader = super.getCharacterStream();

		// Read the beginning of the file to get the BOM
		byte[] buffer = new byte[BUFFER_LENGTH];
		try {
			// Read 3 bytes
			for (int i = 0; i < buffer.length; i++) {
				buffer[i] = (byte) reader.read();
			}

			int skip = 0;

			// UTF-8 byte order mark (length 3 bytes)
			if (Arrays.equals(BOM_UTF8, buffer)) {
				skip = BOM_UTF8.length;
			}
			// UTF-16 byte order mark (length 2 bytes)
			else {
				byte[] compareBuffer = new byte[BOM_UTF16_BIG.length];
				System.arraycopy(buffer, 0, compareBuffer, 0,
						compareBuffer.length);

				// Big and little endian
				if (Arrays.equals(BOM_UTF16_BIG, compareBuffer)
						|| Arrays.equals(BOM_UTF16_LIT, compareBuffer)) {
					skip = BOM_UTF16_BIG.length;
				}
			}

			// Reset not supported, a new reader must be created
			FileReader fr = new FileReader(iFileName);
			fr.skip(skip);

			// Close the old reader
			reader.close();

			// Set the new reader back to the super class
			super.setCharacterStream(fr);
		} catch (Exception e) {
			// Ignore errors, original (unfiltered) stream will be returned
		}

		return super.getCharacterStream();
	}

}
