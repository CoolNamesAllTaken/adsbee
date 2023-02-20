% Stolen from https://github.com/analogdevicesinc/MathWorks_tools/blob/master/hil_models/legacy/ADSB_transmitter/adsbTxGen.m



function [originalData, txData] = ads_b_tx_gen(msg)
% Generate ADSB messages to transmit
% Input msg: ADSB messages characters
% Example: txData = adsbTxGen('8D86D5E058135037C0A9112B72B7');

% Copyright 2016, The MathWorks, Inc.

% Preamble
syncPattern = logical([1 0 1 0 0 0 0 1 0 1 0 0 0 0 0 0]);

% Convert msg characters to bits
msgsz=size(msg);
msgBits = logical(zeros(msgsz(1),4*msgsz(2)));
for ii=1:msgsz(1)
    for jj=1:msgsz(2)
        decNum = hex2dec(msg(ii,jj));
        msgBits(ii,(jj-1)*4+1:jj*4) = logical(fliplr(de2bi(decNum,4)));
    end
end

% Build ADSB waveform
sz=size(msgBits);
adsbWF = false(sz(1),sz(2)*2+length(syncPattern));
for jj=1:sz(1)
    adsbWF(jj,1:16) = syncPattern;
    for ii=1:sz(2)
        if msgBits(jj,ii) == 1
            adsbWF(jj,16+(ii-1)*2+1:16+ii*2) = [true false];
        else
            adsbWF(jj,16+(ii-1)*2+1:16+ii*2) = [false true];
        end
    end
end

% Add zeros to the end of the waveform
##wfsz = size(adsbWF);
##wfLength=wfsz(2);
##txZeros = single(complex(zeros(wfLength*49,1)));
##ppm = single(adsbWF.');
##originalData=[ppm(:,1);txZeros];
originalData = adsbWF;
originalData = repelem(originalData, 5); % each sample is 100ns

% Resample the waveform
txData = resample(double(originalData),4,10);

% Add noise and scale
txData = awgn(txData,80)*1e-4;

end
