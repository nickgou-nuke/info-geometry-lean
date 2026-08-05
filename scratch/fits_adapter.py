from dataclasses import dataclass
import numpy as np
try:
    from astropy.io import fits
except ImportError:
    fits = None

@dataclass(frozen=True)
class CalibratedFrame:
    electrons: np.ndarray
    invalid_mask: np.ndarray
    saturation_mask: np.ndarray
    gain_e_per_adu: np.ndarray | float
    pedestal_adu: np.ndarray | float
    exposure_s: float | None
    temperature_c: float | None
    header: dict

class FitsAdapter:
    def __init__(self, default_gain=1.0, default_pedestal=0.0, saturation_adu=65535):
        self.default_gain = default_gain
        self.default_pedestal = default_pedestal
        self.saturation_adu = saturation_adu

    def load_frame(self, filepath: str, ext: int = 0) -> CalibratedFrame:
        if fits is None:
            raise ImportError("astropy is required to read FITS files.")
            
        with fits.open(filepath) as hdul:
            hdu = hdul[ext]
            data_adu = hdu.data.astype(np.float32)
            header = dict(hdu.header)
            
            # Extract basic metadata with fallback
            gain = header.get('GAIN', self.default_gain)
            pedestal = header.get('PEDESTAL', self.default_pedestal)
            exptime = header.get('EXPTIME', None)
            temp = header.get('CCD-TEMP', None)
            
            # Note: Negative electrons are explicitly preserved! No clipping.
            electrons = gain * (data_adu - pedestal)
            
            # Hard structural domain checks (NaNs, Infs)
            invalid_mask = ~np.isfinite(data_adu)
            
            # Saturated pixels
            saturation_mask = (data_adu >= self.saturation_adu)
            
            return CalibratedFrame(
                electrons=electrons,
                invalid_mask=invalid_mask,
                saturation_mask=saturation_mask,
                gain_e_per_adu=gain,
                pedestal_adu=pedestal,
                exposure_s=exptime,
                temperature_c=temp,
                header=header
            )
