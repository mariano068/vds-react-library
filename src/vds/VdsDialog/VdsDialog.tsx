import { Dialog, DialogProps } from '@mui/material';
import { styled } from '@mui/material/styles';

export type VariantType = 'error' | 'default';

export type VdsDialogProps = DialogProps & { variant?: VariantType };

export const VdsDialog = styled(Dialog)
    (({ variant }: VdsDialogProps) => ({
        '& .MuiPaper': {
            borderRadius: 'unset'
        },
        '& .MuiDialogTitle-root': {
            color: '#005075',
            borderBottom: variant === 'error' ? '2px solid #D82829' : '2px solid #0090D1',
            backgroundColor: 'white'
        },
        '& .MuiDialogActions-root': {
            backgroundColor: '#F2F5F8'
        },
        '& .MuiDialogContent-root': {
            marginTop: '20px'
        },
        '& .MuiDialogContent-dividers': {
            border: 'unset'
        }
    }));
