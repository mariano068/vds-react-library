import { Grid } from '@mui/material'
import * as React from 'react'
import { VdsChip } from '../../vds/VdsChip/VdsChip'
import { convert } from '../utils'

//#region Default chip
export const default_chip_snippet = convert(`
import React from 'react';
import { VdsChip } from 'vds-components';

export default () => {

    const onDeleteHandler: React.MouseEventHandler<HTMLAnchorElement> = (ev) => console.dir(ev);

    return (
      <VdsChip label='Chip 2' onDelete={onDeleteHandler} />
    );
}
`)
export const Default_Chip_Example = () => {

  return (
    <Grid container spacing={2}>
      <Grid item lg={6}>
        <div>
          <VdsChip label='Chip 1' />
          <div>
            <h4>Default</h4>
          </div>
        </div>
      </Grid>
      <Grid item lg={6}>
        <div>
          <VdsChip label='Chip 2' onDelete={() => { }} />
          <div>
            <h4>Chip With Icon</h4>
          </div>
        </div>
      </Grid>
    </Grid>
  )
}
//#endregion
