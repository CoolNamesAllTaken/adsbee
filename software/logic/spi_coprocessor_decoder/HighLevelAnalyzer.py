# High Level Analyzer
# For more information and documentation, please go to https://support.saleae.com/extensions/high-level-analyzer-extensions

from saleae.analyzers import HighLevelAnalyzer, AnalyzerFrame, StringSetting, NumberSetting, ChoicesSetting


# High level analyzers must subclass the HighLevelAnalyzer class.
class SPICoprocessorPacket(HighLevelAnalyzer):

    cmd_strs = {
            0x0: 'kCmdInvalid',
            0x01: 'kCmdWriteToSlave',
            0x02: 'kCmdWriteToSlaveRequireAck',
            0x03: 'kCmdReadFromSlave',
            0x04: 'kCmdWriteToMaster',
            0x05: 'kCmdWriteToMasterRequireAck',
            0x06: 'kCmdReadFromMaster',
            0x07: 'kCmdDataBlock',
            0x08: 'kCmdAck'
    }

    addr_strs = {
        0x0: 'kAddrInvalid', 
        0x01: 'kAddrFirmwareVersion', 
        0x02: 'kAddrScratch', 
        0x03: 'kAddrSettingsData',
        0x04: 'kAddrRawTransponderPacket',
        0x05: 'kAddrDecodedTransponderPacket',
        0x0B: 'kAddrRawTransponderPacketArray',
        0x0C: 'kAddrDecodedTransponderPacketArray',
        0x06: 'kAddrBaseMAC',
        0x07: 'kAddrWiFiStationMAC',
        0x08: 'kAddrWiFiAccessPointMAC',
        0x09: 'kAddrBluetoothMAC',
        0xA: 'kAddrConsole'
    }

    # An optional list of types this analyzer produces, providing a way to customize the way frames are displayed in Logic 2.
    result_types = {
        'generic': {
            'format': 'cmd={{cmd}}\naddr={{addr}}\noffset={{offset}}\n{{len}}\n'
        }
    }

    def __init__(self):
        '''
        Initialize HLA.

        Settings can be accessed using the same name used above.
        '''

        print("Settings: None")

    def decode(self, frame: AnalyzerFrame):
        '''
        Process a frame from the input analyzer, and optionally return a single `AnalyzerFrame` or a list of `AnalyzerFrame`s.

        The type and data values in `frame` will depend on the input analyzer.
        '''
        try:
            if frame.type == "result":
                
                cmd = frame.data['miso'][0]
                cmd_str = self.cmd_strs[cmd]
            else:
                cmd = -1
            
        except:
            print(f"Failed to decode SPICoprocessorPacket with data: {frame.data}")
            return

        # Return the data frame itself
        return AnalyzerFrame('generic', frame.start_time, frame.end_time, {
            'cmd': cmd
        })
